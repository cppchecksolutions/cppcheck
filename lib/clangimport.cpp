/*
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2026 Cppcheck team.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "clangimport.h"

#include "errortypes.h"
#include "mathlib.h"
#include "refthunk.h"
#include "standards.h"
#include "symboldatabase.h"
#include "token.h"
#include "tokenize.h"
#include "tokenlist.h"
#include "utils.h"
#include "vfvalue.h"

#include <algorithm>
#include <cctype>
#include <cstring>
#include <iostream>
#include <iterator>
#include <list>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include <numeric>

#include "json.h"

/*
 * Import of the clang AST, "clang -Xclang -ast-dump=json"
 *
 * The JSON is converted into tokens and a symbol database, the same as the
 * normal tokenizer and symbol database would create for the code. The goal is
 * that the checkers see the same data with and without --clang.
 *
 * Steps:
 *  1. parse the JSON with picojson
 *  2. pre-passes over the JSON: complete the locations, collect label names
 *     and typedef names
 *  3. each top level declaration is converted into an AstNode tree
 *     (parseTree) and tokens are created (AstNode::createTokens). The scopes,
 *     variables, functions and types of the symbol database are created at
 *     the same time.
 *  4. the remaining symbol database information is filled in
 *
 * Some details about the clang JSON:
 *  - the "kind" of a node is the clang class name: "VarDecl", "IfStmt", ..
 *  - declarations have an "id", references to declarations use that id
 *  - "file" and "line" are only written when they change
 *  - qualifiers "N::" are not written in a DeclRefExpr
 *  - anonymous types are written as "(unnamed struct at file:line:col)"
 *  - clang adds implicit nodes ("isImplicit", implicit casts, default
 *    arguments, ..), these are not written as tokens
 */

// node kinds
static const std::string AccessSpecDecl = "AccessSpecDecl";
static const std::string ArraySubscriptExpr = "ArraySubscriptExpr";
static const std::string BinaryOperator = "BinaryOperator";
static const std::string BreakStmt = "BreakStmt";
static const std::string CallExpr = "CallExpr";
static const std::string CaseStmt = "CaseStmt";
static const std::string CharacterLiteral = "CharacterLiteral";
static const std::string ClassTemplateDecl = "ClassTemplateDecl";
static const std::string ClassTemplateSpecializationDecl = "ClassTemplateSpecializationDecl";
static const std::string ConditionalOperator = "ConditionalOperator";
static const std::string ConstantExpr = "ConstantExpr";
static const std::string CompoundAssignOperator = "CompoundAssignOperator";
static const std::string CompoundStmt = "CompoundStmt";
static const std::string ContinueStmt = "ContinueStmt";
static const std::string CStyleCastExpr = "CStyleCastExpr";
static const std::string CXXBindTemporaryExpr = "CXXBindTemporaryExpr";
static const std::string CXXBoolLiteralExpr = "CXXBoolLiteralExpr";
static const std::string CXXCatchStmt = "CXXCatchStmt";
static const std::string CXXConstCastExpr = "CXXConstCastExpr";
static const std::string CXXConstructorDecl = "CXXConstructorDecl";
static const std::string CXXConstructExpr = "CXXConstructExpr";
static const std::string CXXCtorInitializer = "CXXCtorInitializer";
static const std::string CXXDefaultArgExpr = "CXXDefaultArgExpr";
static const std::string CXXDefaultInitExpr = "CXXDefaultInitExpr";
static const std::string CXXDeleteExpr = "CXXDeleteExpr";
static const std::string CXXDestructorDecl = "CXXDestructorDecl";
static const std::string CXXDynamicCastExpr = "CXXDynamicCastExpr";
static const std::string CXXForRangeStmt = "CXXForRangeStmt";
static const std::string CXXFunctionalCastExpr = "CXXFunctionalCastExpr";
static const std::string CXXMemberCallExpr = "CXXMemberCallExpr";
static const std::string CXXMethodDecl = "CXXMethodDecl";
static const std::string CXXNewExpr = "CXXNewExpr";
static const std::string CXXNullPtrLiteralExpr = "CXXNullPtrLiteralExpr";
static const std::string CXXOperatorCallExpr = "CXXOperatorCallExpr";
static const std::string CXXRecordDecl = "CXXRecordDecl";
static const std::string CXXReinterpretCastExpr = "CXXReinterpretCastExpr";
static const std::string CXXStaticCastExpr = "CXXStaticCastExpr";
static const std::string CXXStdInitializerListExpr = "CXXStdInitializerListExpr";
static const std::string CXXTemporaryObjectExpr = "CXXTemporaryObjectExpr";
static const std::string CXXThisExpr = "CXXThisExpr";
static const std::string CXXThrowExpr = "CXXThrowExpr";
static const std::string CXXTryStmt = "CXXTryStmt";
static const std::string DeclRefExpr = "DeclRefExpr";
static const std::string DeclStmt = "DeclStmt";
static const std::string DefaultStmt = "DefaultStmt";
static const std::string DoStmt = "DoStmt";
static const std::string EnumConstantDecl = "EnumConstantDecl";
static const std::string EnumDecl = "EnumDecl";
static const std::string ExprWithCleanups = "ExprWithCleanups";
static const std::string FieldDecl = "FieldDecl";
static const std::string FloatingLiteral = "FloatingLiteral";
static const std::string ForStmt = "ForStmt";
static const std::string FunctionDecl = "FunctionDecl";
static const std::string FunctionTemplateDecl = "FunctionTemplateDecl";
static const std::string GotoStmt = "GotoStmt";
static const std::string IfStmt = "IfStmt";
static const std::string ImplicitCastExpr = "ImplicitCastExpr";
static const std::string ImplicitValueInitExpr = "ImplicitValueInitExpr";
static const std::string InitListExpr = "InitListExpr";
static const std::string IntegerLiteral = "IntegerLiteral";
static const std::string LabelStmt = "LabelStmt";
static const std::string LambdaExpr = "LambdaExpr";
static const std::string LinkageSpecDecl = "LinkageSpecDecl";
static const std::string MaterializeTemporaryExpr = "MaterializeTemporaryExpr";
static const std::string MemberExpr = "MemberExpr";
static const std::string NamespaceDecl = "NamespaceDecl";
static const std::string NullStmt = "NullStmt";
static const std::string ParenExpr = "ParenExpr";
static const std::string ParmVarDecl = "ParmVarDecl";
static const std::string RecordDecl = "RecordDecl";
static const std::string ReturnStmt = "ReturnStmt";
static const std::string StringLiteral = "StringLiteral";
static const std::string SwitchStmt = "SwitchStmt";
static const std::string TemplateArgument = "TemplateArgument";
static const std::string TranslationUnitDecl = "TranslationUnitDecl";
static const std::string TypedefDecl = "TypedefDecl";
static const std::string UnaryOperator = "UnaryOperator";
static const std::string UsingDirectiveDecl = "UsingDirectiveDecl";
static const std::string UnaryExprOrTypeTraitExpr = "UnaryExprOrTypeTraitExpr";
static const std::string VarDecl = "VarDecl";
static const std::string WhileStmt = "WhileStmt";

// ---------------------------------------------------------------------------
// Reading values from the clang JSON
// ---------------------------------------------------------------------------

/** string value obj[key], defaultValue if there is no such string */
static std::string getJsonString(const picojson::object &obj, const std::string &key, const std::string &defaultValue = "")
{
    const auto it = obj.find(key);
    return (it != obj.end() && it->second.is<std::string>()) ? it->second.get<std::string>() : defaultValue;
}

/** bool value obj[key], false if there is no such bool */
static bool getJsonBool(const picojson::object &obj, const std::string &key)
{
    const auto it = obj.find(key);
    return it != obj.end() && it->second.is<bool>() && it->second.get<bool>();
}

/** object value obj[key], nullptr if there is no such object */
static const picojson::object *findJsonObject(const picojson::object &obj, const std::string &key)
{
    const auto it = obj.find(key);
    return (it != obj.end() && it->second.is<picojson::object>()) ? &it->second.get<picojson::object>() : nullptr;
}

/** type obj[key] = {"qualType": ".."} => qualType */
static std::string getJsonQualType(const picojson::object &obj, const std::string &key)
{
    const picojson::object *type = findJsonObject(obj, key);
    return type ? getJsonString(*type, "qualType") : "";
}

/** Location in source file. For macros this is where the macro is used. */
static const picojson::object &getFileLocation(const picojson::object &loc)
{
    if (const picojson::object *expansionLoc = findJsonObject(loc, "expansionLoc"))
        return *expansionLoc;
    return loc;
}

/** "begin" or "end" location of the range of a node, nullptr if it is not written */
static const picojson::object *getRangeLocation(const picojson::object &node, const char *where)
{
    const picojson::object *range = findJsonObject(node, "range");
    return range ? findJsonObject(*range, where) : nullptr;
}

/** read "file", "line" and "col" of a location, values that are not written are not changed */
static void readLocation(TokenList &tokenList, const picojson::object &location, int &file, int &line, int &col)
{
    const picojson::object &loc = getFileLocation(location);
    if (loc.count("file") && loc.at("file").is<std::string>())
        file = tokenList.appendFileIfNew(loc.at("file").get<std::string>());
    if (loc.count("line") && loc.at("line").is<int64_t>())
        line = loc.at("line").get<int64_t>();
    if (loc.count("col") && loc.at("col").is<int64_t>())
        col = loc.at("col").get<int64_t>();
}

/** scope of tok. The import creates the symbol database so the scope can be modified. */
static Scope *getTokenScope(const Token *tok)
{
    return const_cast<Scope *>(tok->scope());
}

/** file offset of a location, -1 if it is unknown */
static int64_t getLocationOffset(const picojson::object *location)
{
    if (!location)
        return -1;
    const picojson::object &loc = getFileLocation(*location);
    return (loc.count("offset") && loc.at("offset").is<int64_t>()) ? loc.at("offset").get<int64_t>() : -1;
}


/** split a type into tokens: "unsigned int *" => "unsigned", "int", "*" */
static std::vector<std::string> splitString(const std::string &line)
{
    std::vector<std::string> ret;

    // array dimensions "[2][n + 1]"
    if (!line.empty() && line[0] == '[') {
        std::string::size_type pos = 0;
        while (pos < line.size()) {
            if (line[pos] == ' ') {
                ++pos;
                continue;
            }
            std::string::size_type end = pos + 1;
            if (std::isalnum(static_cast<unsigned char>(line[pos])) || line[pos] == '_') {
                while (end < line.size() && (std::isalnum(static_cast<unsigned char>(line[end])) || line[end] == '_'))
                    ++end;
            }
            ret.push_back(line.substr(pos, end - pos));
            pos = end;
        }
        return ret;
    }

    std::string::size_type pos1 = line.find_first_not_of(' ');
    while (pos1 < line.size()) {
        std::string::size_type pos2;
        if (std::strchr("*()", line[pos1])) {
            ret.push_back(line.substr(pos1,1));
            pos1 = line.find_first_not_of(' ', pos1 + 1);
            continue;
        }
        pos2 = pos1;
        while (pos2 < line.size() && (line[pos2] == '_' || line[pos2] == ':' || std::isalnum(static_cast<unsigned char>(line[pos2]))))
            ++pos2;
        if (pos2 > pos1 && pos2 < line.size() && line[pos2] == '<' && std::isalpha(line[pos1])) {
            int tlevel = 1;
            while (++pos2 < line.size() && tlevel > 0) {
                if (line[pos2] == '<')
                    ++tlevel;
                else if (line[pos2] == '>')
                    --tlevel;
            }
            if (tlevel == 0 && pos2 < line.size() && line[pos2] == ' ') {
                ret.push_back(line.substr(pos1, pos2-pos1));
                pos1 = pos2 + 1;
                continue;
            }
        }

        pos2 = line.find(' ', pos1) - 1;
        if ((std::isalpha(line[pos1]) || line[pos1] == '_') &&
            line.find("::", pos1) < pos2 &&
            line.find("::", pos1) < line.find('<', pos1)) {
            pos2 = line.find("::", pos1);
            ret.push_back(line.substr(pos1, pos2-pos1));
            ret.emplace_back("::");
            pos1 = pos2 + 2;
            continue;
        }
        if ((std::isalpha(line[pos1]) || line[pos1] == '_') &&
            line.find('<', pos1) < pos2 &&
            line.find("<<",pos1) != line.find('<',pos1) &&
            line.find('>', pos1) != std::string::npos &&
            line.find('>', pos1) > pos2) {
            int level = 0;
            for (pos2 = pos1; pos2 < line.size(); ++pos2) {
                if (line[pos2] == '<')
                    ++level;
                else if (line[pos2] == '>') {
                    if (level <= 1)
                        break;
                    --level;
                }
            }
            if (level > 1 && pos2 + 1 >= line.size())
                return std::vector<std::string> {};
            pos2 = line.find(' ', pos2);
            if (pos2 != std::string::npos)
                --pos2;
        }
        if (pos2 == std::string::npos) {
            ret.push_back(line.substr(pos1));
            break;
        }
        ret.push_back(line.substr(pos1, pos2+1-pos1));
        pos1 = line.find_first_not_of(' ', pos2 + 1);
    }
    return ret;
}

/** position of the name in a declaration: "int [3]" => "int x[3]", "int (*)(int)" => "int (*x)(int)" */
static std::string::size_type getDeclaratorNamePos(const std::string& qualType) {
    std::string::size_type par = qualType.find("(*");
    if (par == std::string::npos)
        par = qualType.find("(&");
    if (par != std::string::npos) {
        std::string::size_type pos = par + 1;
        while (pos < qualType.size() && (qualType[pos] == '*' || qualType[pos] == '&'))
            ++pos;
        return pos;
    }
    return qualType.find('[');
}

/** type before the name: "int [3]" => "int" */
static std::string getQualTypeBefore(const std::string& qualType) {
    const std::string::size_type pos = getDeclaratorNamePos(qualType);
    return pos != std::string::npos ? qualType.substr(0, pos) : qualType;
}

/** type after the name: "int [3]" => "[3]" */
static std::string getQualTypeAfter(const std::string& qualType) {
    const std::string::size_type pos = getDeclaratorNamePos(qualType);
    return pos != std::string::npos ? qualType.substr(pos) : "";
}

namespace clangimport {
    /**
     * Data that is shared by all nodes during the import: the declarations
     * (id => variable/function/enumerator/scope) and the state of the import.
     */
    struct Data {
        /** A declaration of a variable, function or enumerator, tokens that refer to it get the variable/function/enumerator */
        struct Decl {
            explicit Decl(Variable *var) : var(var) {}
            explicit Decl(Function *function) : function(function) {}
            explicit Decl(Enumerator *enumerator) : enumerator(enumerator) {}
            /** let tok refer to this declaration */
            void ref(Token *tok) const {
                if (enumerator)
                    tok->enumerator(enumerator);
                if (function) {
                    // a function name has no value type
                    tok->function(function);
                    tok->setValueType(nullptr);
                }
                if (var) {
                    tok->variable(var);
                    tok->varId(var->declarationId());
                    // same as the normal import: the value type of a variable is the declared type "const V &"
                    if (var->valueType())
                        tok->setValueType(new ValueType(*var->valueType()));
                }
            }
            Enumerator* enumerator{};
            Function* function{};
            Variable* var{};
        };

        Data(const Settings& settings, SymbolDatabase& symbolDatabase)
            : mSettings(settings)
            , mSymbolDatabase(symbolDatabase)
        {}

        RefThunk<const Settings> mSettings;
        RefThunk<SymbolDatabase> mSymbolDatabase;

        /** value of the next enumerator */
        MathLib::bigint enumValue = 0;
        /** "file:line:col" of anonymous type => name of the type */
        std::map<std::string, std::string> mAnonymousTypes;

        /** "typedef struct { .. } T;" => the anonymous struct is named T */
        std::map<std::string, std::string> mTypedefNames;

        /** name for anonymous enum/struct: typedef name or Anonymous<N> */
        std::string getAnonymousTypeName(const std::string &id, const std::string &location) {
            const auto it = mTypedefNames.find(id);
            if (it == mTypedefNames.end())
                return addAnonymousType(location);
            mAnonymousTypes[location] = it->second;
            return it->second;
        }

        /** label names, GotoStmt only has the id of the label */
        std::map<std::string, std::string> mLabelNames;

        /** Anonymous enum/struct, clang refers to it by location: "(unnamed enum at file:line:col)" */
        std::string addAnonymousType(const std::string &location) {
            std::string name = "Anonymous" + std::to_string(mAnonymousTypes.size());
            mAnonymousTypes[location] = name;
            return name;
        }

        /** Replace "(unnamed enum at file:line:col)" with "Anonymous0" */
        std::string replaceAnonymousTypes(std::string type) const {
            std::string::size_type pos1;
            while ((pos1 = type.find("(unnamed ")) != std::string::npos) {
                const std::string::size_type at = type.find(" at ", pos1);
                const std::string::size_type pos2 = type.find(')', pos1);
                if (at == std::string::npos || pos2 == std::string::npos || at > pos2)
                    break;
                const auto it = mAnonymousTypes.find(type.substr(at + 4, pos2 - at - 4));
                if (it == mAnonymousTypes.end())
                    break;
                // remove qualification "O::(unnamed struct at ..)", the anonymous type is used where it is declared
                while (pos1 >= 2 && type.compare(pos1 - 2, 2, "::") == 0) {
                    std::string::size_type start = pos1 - 2;
                    while (start > 0 && (std::isalnum(static_cast<unsigned char>(type[start - 1])) || type[start - 1] == '_'))
                        --start;
                    pos1 = start;
                }
                type.replace(pos1, pos2 + 1 - pos1, it->second);
            }
            return type;
        }

        // Declarations. References that were seen before the declaration are resolved.

        void enumDecl(const std::string &addr, Token *nameToken, Enumerator *enumerator) {
            mDeclMap.emplace(addr, Decl(enumerator));
            nameToken->enumerator(enumerator);
            notFound(addr);
        }

        void funcDecl(const std::string &id, Token *nameToken, Function *function) {
            mDeclMap.emplace(id, Decl(function));
            nameToken->function(function);
            notFound(id);
        }

        /** namespace/record declaration */
        void scopeDecl(const std::string &addr, Scope *scope) {
            mScopeMap.emplace(addr, scope);
        }

        /** variable declaration, a new varid is created */
        void varDecl(const std::string &addr, Token *def, Variable *var) {
            mDeclMap.emplace(addr, Decl(var));
            def->varId(++mVarId);
            def->variable(var);
            if (def->valueType())
                var->setValueType(*def->valueType());
            notFound(addr);
        }

        /** the variable is moved: "for (int i = 0;..)" => i is moved to the for scope */
        void replaceVarDecl(const Variable *from, Variable *to) {
            for (auto &it: mDeclMap) {
                Decl &decl = it.second;
                if (decl.var == from)
                    decl.var = to;
            }
        }

        /** tok refers to declaration id. If the declaration is not seen yet, it is resolved later. */
        void ref(const std::string &id, Token *tok) {
            auto it = mDeclMap.find(id);
            if (it != mDeclMap.end())
                it->second.ref(tok);
            else
                mNotFound[id].push_back(tok);
        }

        /** varid => variable, for the symbol database */
        std::vector<const Variable *> getVariableList() const {
            std::vector<const Variable *> ret;
            ret.resize(mVarId + 1, nullptr);
            for (const auto& it: mDeclMap) {
                if (it.second.var)
                    ret[it.second.var->declarationId()] = it.second.var;
            }
            for (const auto& it: mMemberVarIds)
                ret[it.second.first] = it.second.second;
            return ret;
        }

        /** varid for member access "s.x", same as the normal tokenizer: one varid for each object+member */
        int memberVarId(int objectVarId, const Variable *member) {
            auto it = mMemberVarIds.find(std::make_pair(objectVarId, member));
            if (it != mMemberVarIds.end())
                return it->second.first;
            const int varId = ++mVarId;
            mMemberVarIds[std::make_pair(objectVarId, member)] = std::make_pair(varId, member);
            return varId;
        }

        bool hasDecl(const std::string &id) const {
            return mDeclMap.find(id) != mDeclMap.end();
        }

        /** scope where a variable/function/enumerator is declared */
        const Scope *getDeclScope(const std::string &id) const {
            auto it = mDeclMap.find(id);
            if (it == mDeclMap.end())
                return nullptr;
            const Decl &decl = it->second;
            if (decl.var)
                return decl.var->scope();
            if (decl.function)
                return decl.function->nestedIn;
            if (decl.enumerator) {
                const Scope *enumScope = decl.enumerator->scope;
                // enumerators of unscoped enums are declared in the enclosing scope
                return (enumScope && !enumScope->enumClass) ? enumScope->nestedIn : enumScope;
            }
            return nullptr;
        }

        /** scope of a namespace/record declaration */
        Scope *getScope(const std::string &id) {
            auto it = mScopeMap.find(id);
            return (it == mScopeMap.end() ? nullptr : it->second);
        }

        // "}" tokens that are not end-of-scope
        std::set<const Token *> mNotScope;

        /** current access in classes: "public:" etc */
        std::map<const Scope *, AccessControl> scopeAccessControl;
    private:
        /** resolve references that were seen before the declaration */
        void notFound(const std::string &addr) {
            auto it = mNotFound.find(addr);
            if (it != mNotFound.end()) {
                for (Token *reftok: it->second)
                    ref(addr, reftok);
                mNotFound.erase(it);
            }
        }

        /** id => declaration */
        std::map<std::string, Decl> mDeclMap;
        /** id => scope of namespace/record */
        std::map<std::string, Scope *> mScopeMap;
        /** (object varid, member) => (member varid, member) */
        std::map<std::pair<int, const Variable *>, std::pair<int, const Variable *>> mMemberVarIds;
        /** id => tokens that refer to a declaration that is not seen yet */
        std::map<std::string, std::vector<Token *>> mNotFound;
        /** last varid */
        int mVarId = 0;
    };

    class AstNode;
    using AstNodePtr = std::shared_ptr<AstNode>;

    /**
     * A node in the clang AST. The tokens for the node and its children are
     * created by createTokens.
     */
    class AstNode {
    public:
        AstNode(const picojson::object& jsonObject, Data &data)
            : mKind(jsonObject.at("kind").get<std::string>())
            , mJsonObject(jsonObject)
            , mData(data)
        {}
        const std::string mKind;
        std::vector<AstNodePtr> children;

        /** declaration that clang adds: builtin typedefs, implicit constructors, .. */
        bool isImplicit() const;
        /** default argument or value that clang adds in an initializer */
        bool isImplicitInit() const {
            return mKind == CXXDefaultArgExpr || mKind == CXXDefaultInitExpr || mKind == ImplicitValueInitExpr;
        }
        /** "file:line:col", clang uses that for anonymous types */
        std::string getLocationString(const TokenList &tokenList) const {
            return tokenList.getFiles()[mFile] + ":" + std::to_string(mLine) + ":" + std::to_string(mCol);
        }
        /**
         * @throws InternalError thrown if AST location is invalid
         */
        void setLocations(TokenList &tokenList, int file, int line, int col);

        void dumpAst(int num = 0, int indent = 0) const;
        /** create tokens for a top level declaration */
        void createTokens1(TokenList &tokenList) {
            //dumpAst(); // TODO: reactivate or remove
            if (isImplicit() || mKind == TypedefDecl)
                return; // typedefs are not needed, clang writes the actual types

            if (!tokenList.back()) {
                setLocations(tokenList, 0, 1, 1);
            }
            else
                setLocations(tokenList, tokenList.back()->fileIndex(), tokenList.back()->linenr(), 1);
            createTokens(tokenList);
            if (mKind == VarDecl)
                addtokenAtRange(tokenList, ";", "end");
            mData.mNotScope.clear();
        }

        /**
         * @throws InternalError thrown if index is out of bounds
         */
        AstNodePtr getChild(size_t c) {
            if (c >= children.size()) {
                std::ostringstream err;
                err << "ClangImport: AstNodePtr::getChild(" << c << ") out of bounds. children.size=" << children.size() << " " << mKind << " " << getId();
                throw InternalError(nullptr, err.str());
            }
            return children[c];
        }

        const picojson::object& getJsonObject() const {
            return mJsonObject;
        }

        /** id of the node, references to a declaration use the id */
        std::string getId() const {
            return getJsonString(mJsonObject, "id");
        }

    private:
        /**
         * create tokens for this node and its children
         * @return the token that is the root of the AST for an expression
         * @throws InternalError thrown if CXXForRangeStmt cannot be imported
         */
        Token *createTokens(TokenList &tokenList);
        // createTokens for the node kinds
        Token *createTokensKeyword(TokenList &tokenList);
        Token *createTokensFirstChild(TokenList &tokenList);
        Token *createTokensCXXTemporaryObjectExpr(TokenList &tokenList);
        Token *createTokensValue(TokenList &tokenList);
        Token *createTokensIgnored(TokenList &tokenList);
        Token *createTokensVariable(TokenList &tokenList);
        Token *createTokensFunction(TokenList &tokenList);
        Token *createTokensRecord(TokenList &tokenList);
        Token *createTokensArraySubscriptExpr(TokenList &tokenList);
        Token *createTokensBinaryOperator(TokenList &tokenList);
        Token *createTokensCharacterLiteral(TokenList &tokenList);
        Token *createTokensCaseStmt(TokenList &tokenList);
        Token *createTokensClassTemplateDecl(TokenList &tokenList);
        Token *createTokensConditionalOperator(TokenList &tokenList);
        Token *createTokensCompoundStmt(TokenList &tokenList);
        Token *createTokensCStyleCastExpr(TokenList &tokenList);
        Token *createTokensCXXBoolLiteralExpr(TokenList &tokenList);
        Token *createTokensCXXConstructExpr(TokenList &tokenList);
        Token *createTokensCXXDeleteExpr(TokenList &tokenList);
        Token *createTokensCXXForRangeStmt(TokenList &tokenList);
        Token *createTokensCXXMethodDecl(TokenList &tokenList);
        Token *createTokensCXXNewExpr(TokenList &tokenList);
        Token *createTokensCXXNamedCastExpr(TokenList &tokenList);
        Token *createTokensCXXFunctionalCastExpr(TokenList &tokenList);
        Token *createTokensCXXThrowExpr(TokenList &tokenList);
        Token *createTokensCXXTryStmt(TokenList &tokenList);
        Token *createTokensCXXCatchStmt(TokenList &tokenList);
        Token *createTokensDeclRefExpr(TokenList &tokenList);
        Token *createTokensDeclStmt(TokenList &tokenList);
        Token *createTokensDefaultStmt(TokenList &tokenList);
        Token *createTokensDoStmt(TokenList &tokenList);
        Token *createTokensEnumConstantDecl(TokenList &tokenList);
        Token *createTokensEnumDecl(TokenList &tokenList);
        Token *createTokensFloatingLiteral(TokenList &tokenList);
        Token *createTokensForStmt(TokenList &tokenList);
        Token *createTokensFunctionTemplateDecl(TokenList &tokenList);
        Token *createTokensGotoStmt(TokenList &tokenList);
        Token *createTokensIfStmt(TokenList &tokenList);
        Token *createTokensImplicitCastExpr(TokenList &tokenList);
        Token *createTokensInitListExpr(TokenList &tokenList);
        Token *createTokensLabelStmt(TokenList &tokenList);
        Token *createTokensMemberExpr(TokenList &tokenList);
        Token *createTokensNamespaceDecl(TokenList &tokenList);
        Token *createTokensUsingDirectiveDecl(TokenList &tokenList);
        Token *createTokensParenExpr(TokenList &tokenList);
        Token *createTokensRecordDecl(TokenList &tokenList);
        Token *createTokensReturnStmt(TokenList &tokenList);
        Token *createTokensSwitchStmt(TokenList &tokenList);
        Token *createTokensTypedefDecl(TokenList &tokenList);
        Token *createTokensUnaryOperator(TokenList &tokenList);
        Token *createTokensUnaryExprOrTypeTraitExpr(TokenList &tokenList);
        Token *createTokensWhileStmt(TokenList &tokenList);
        /** add token at the location of this node, the scope is set and the value type is set if valueType is true */
        Token *addtoken(TokenList &tokenList, const std::string &str, bool valueType=true);
        /** ": ;" after a label/case/default, same as the normal tokenizer */
        void addLabelColon(TokenList &tokenList) {
            addtoken(tokenList, ":");
            addtoken(tokenList, ";");
        }
        /** add token at the "begin" or "end" location of the range of this node */
        Token *addtokenAtRange(TokenList &tokenList, const std::string &str, const char *where);
        /** add tokens for a type "unsigned int *", returns the record type if the type is a struct/class */
        const ::Type *addTypeTokens(TokenList &tokenList, const std::string &str, const Scope *scope = nullptr);
        /** "S :: " for out of line member functions */
        void addFullScopeNameTokens(TokenList &tokenList, const Scope *recordScope);
        /** "for (int i = 0; ..)", "catch (int e)": the variable is moved from the outer scope to the for/catch scope */
        void moveConditionVariables(const Token *def, Scope *scope);
        /** create scope "{ .. }" for a body */
        Scope *createScope(TokenList &tokenList, ScopeType scopeType, AstNodePtr astNode, const Token *def);
        /** create scope "{ .. }" with tokens for children2. existingScope: reopened namespace */
        Scope *createScope(TokenList &tokenList, ScopeType scopeType, const std::vector<AstNodePtr> &children2, const Token *def, Scope *existingScope = nullptr);
        /** function call "f ( args )" */
        RET_NONNULL Token *createTokensCall(TokenList &tokenList);
        /** "( args )" of a call, the arguments are children[firstArg..] */
        Token *createTokensCallArguments(TokenList &tokenList, Token *f, std::size_t firstArg);
        Token *createTokensCXXOperatorCallExpr(TokenList &tokenList);
        /** "( cond )" after "if", "while", "switch" */
        Token *createTokensCondition(TokenList &tokenList, Token *keyword, const AstNodePtr &cond);
        /** constructor initializer list ": x ( 0 ) , y { 1 }" */
        void createTokensCtorInitializers(TokenList &tokenList);
        /** "( args )" or "{ args }" of a direct initialization */
        Token *createTokensInitArgs(TokenList &tokenList, Token *name);
        /** initialization in a variable declaration "= x", "( x )", "{ x }" */
        Token *createTokensVarInit(TokenList &tokenList, Token *vartok1, const ::Type *recordType);
        /** type tokens before the name in a declaration: "int ( *" in "int (*fp)(int)". Returns the record type. */
        const ::Type *addTypeTokensBeforeName(TokenList &tokenList, const std::string &qualType, std::stack<Token *> &links, const Scope *scope = nullptr);
        /** type tokens after the name in a declaration: "[ 3 ]", ") ( int )" */
        void addTypeTokensAfterName(TokenList &tokenList, const std::string &qualType, std::stack<Token *> &links);
        /** declarator tokens "( *" .. ") ( int )" of a function pointer */
        void addDeclaratorTokens(TokenList &tokenList, const std::string &str, std::stack<Token *> &links);
        /** statement in a block */
        static void createTokensStatement(TokenList &tokenList, const AstNodePtr &stmt);
        /** function declaration/definition, also creates the Function and the function scope */
        void createTokensFunctionDecl(TokenList &tokenList);
        /** the Function for a function declaration, a previous declaration is reused */
        Function *getFunction(const TokenList &tokenList, Token *nameToken, const Token *retDef, const std::string &prev);
        /** scope of a function body */
        Scope *createFunctionScope(Function *function, const Token *nameToken, const Scope *functionOf);
        /**
         * "( args )" of a function declaration, returns the "(".
         * typeScope: where argument types are looked up.
         * declareArgs: the arguments are declared, newFunction: the arguments are added to function.
         */
        Token *createTokensFunctionArguments(TokenList &tokenList, Function *function, Scope *scope, const Scope *typeScope, bool declareArgs, bool newFunction);
        /** "{ .. }" body of function, returns the "{" */
        Token *createTokensFunctionBody(TokenList &tokenList, Scope *scope);
        Token *createTokensLambdaExpr(TokenList &tokenList);
        /** C++ struct/class/union */
        void createTokensForCXXRecord(TokenList &tokenList);
        /** baseVar: "int i, j" => base type for the 2nd declaration "j" is "int" */
        Token *createTokensVarDecl(TokenList &tokenList, const Variable *baseVar = nullptr, const Token *baseTypeEnd = nullptr, const std::string &baseType = "");
        /** name of declaration or operator of an expression */
        std::string getSpelling() const;
        /** name of a struct/union/class/enum, anonymous types get a generated name */
        std::string getTypeName(const TokenList &tokenList) const;
        /** string attribute of the node */
        std::string jsonString(const std::string &key, const std::string &defaultValue = "") const {
            return getJsonString(mJsonObject, key, defaultValue);
        }
        /** bool attribute of the node */
        bool jsonBool(const std::string &key) const {
            return getJsonBool(mJsonObject, key);
        }
        /** type of this node, typedefs are resolved */
        std::string getQualType() const;
        /** "static", "extern" or "" */
        std::string getStorageClass() const;
        /** struct/class/union with body */
        bool isDefinition() const;
        /** "<int,char>" for template instantiation */
        std::string getTemplateParameters() const;
        /** scope for the next token */
        Scope *getNestedInScope(TokenList &tokenList);
        /** set value type of tok to the type of this node */
        void setValueType(Token *tok);
        /** set value type of tok, scope: where record types are looked up */
        void setValueType(Token *tok, const std::string &type, const Scope *scope = nullptr);

        /** location of this node */
        int mFile  = 0;
        int mLine  = 1;
        int mCol   = 1;
        /** the JSON of this node. It is a reference, the parsed JSON lives during the whole import. */
        const picojson::object &mJsonObject;
        Data& mData;
    };
}

std::string clangimport::AstNode::getSpelling() const
{
    if (mJsonObject.count("opcode") > 0)
        return jsonString("opcode");
    return jsonString("name");
}

/** remove qualifiers "X::" */
static std::string removeQualifiers(const std::string &type)
{
    std::string ret;
    std::string::size_type nameStart = 0;
    for (std::string::size_type pos = 0; pos < type.size(); ++pos) {
        const char c = type[pos];
        if (std::isalnum(static_cast<unsigned char>(c)) || c == '_')
            continue;
        if (c == ':' && pos + 1 < type.size() && type[pos + 1] == ':' && pos > nameStart) {
            ++pos;
        } else {
            ret += type.substr(nameStart, pos + 1 - nameStart);
        }
        nameStart = pos + 1;
    }
    return ret + type.substr(std::min(nameStart, type.size()));
}

/** remove qualifiers and keywords "struct", "union", "enum", "class" */
static std::string removeQualifiersAndTagKeywords(const std::string &type)
{
    std::string ret;
    for (const std::string &word: splitString(removeQualifiers(type))) {
        if (word == "struct" || word == "union" || word == "enum" || word == "class")
            continue;
        if (!ret.empty())
            ret += ' ';
        ret += word;
    }
    return ret;
}

std::string clangimport::AstNode::getQualType() const
{
    const picojson::object *type = findJsonObject(mJsonObject, "type");
    if (!type)
        return "";
    const std::string qualType = getJsonString(*type, "qualType");
    if (type->count("desugaredQualType") > 0) {
        // the type is the same, only qualifiers/keywords differ => use the type that is written in the code
        const std::string desugared = getJsonString(*type, "desugaredQualType");
        if (type->count("qualType") > 0 && removeQualifiersAndTagKeywords(desugared) == removeQualifiersAndTagKeywords(qualType))
            return qualType;
        return desugared;
    }
    return qualType;
}

std::string clangimport::AstNode::getTypeName(const TokenList &tokenList) const
{
    std::string name = getSpelling();
    if (name.empty() && (mKind == EnumDecl || isDefinition()))
        name = mData.getAnonymousTypeName(getId(), getLocationString(tokenList));
    return name;
}

std::string clangimport::AstNode::getStorageClass() const
{
    return jsonString("storageClass");
}

bool clangimport::AstNode::isDefinition() const
{
    return jsonBool("completeDefinition");
}

std::string clangimport::AstNode::getTemplateParameters() const
{
    std::string ret;
    for (const AstNodePtr& child: children) {
        if (child->mKind == TemplateArgument)
            ret += (ret.empty() ? "<" : ",") + child->getQualType();
    }
    return ret.empty() ? "" : (ret + ">");
}

// cppcheck-suppress unusedFunction // only used in comment
void clangimport::AstNode::dumpAst(int num, int indent) const
{
    (void)num;
    std::cout << std::string(indent, ' ') << mKind << " " << getId() << " " << getSpelling();
    const std::string type = getQualType();
    if (!type.empty())
        std::cout << " '" << type << "'";
    std::cout << std::endl;
    for (size_t c = 0; c < children.size(); ++c) {
        if (children[c])
            children[c]->dumpAst(c, indent + 2);
        else
            std::cout << std::string(indent + 2, ' ') << "<<<<NULL>>>>>" << std::endl;
    }
}

bool clangimport::AstNode::isImplicit() const
{
    // clang adds builtin typedefs, operator new/delete, etc
    return jsonBool("isImplicit");
}

/** Is declaration in declScope visible in scope without qualification */
static bool isVisibleScope(const Scope *declScope, const Scope *scope)
{
    for (; scope; scope = scope->nestedIn) {
        if (scope == declScope)
            return true;
        if (scope->functionOf && isVisibleScope(declScope, scope->functionOf))
            return true;
        if (std::any_of(scope->usingList.cbegin(), scope->usingList.cend(), [&](const Scope::UsingInfo &u) {
            return u.scope == declScope;
        }))
            return true;
    }
    return false;
}

/** set the location of this node and its children, a node without location gets the location of its parent */
void clangimport::AstNode::setLocations(TokenList &tokenList, int file, int line, int col)
{
    // declarations have a "loc", expressions/statements only have a "range"
    if (const picojson::object *loc = findJsonObject(mJsonObject, "loc"))
        readLocation(tokenList, *loc, file, line, col);
    else if (const picojson::object *begin = getRangeLocation(mJsonObject, "begin"))
        readLocation(tokenList, *begin, file, line, col);
    mFile = file;
    mLine = line;
    mCol = col;
    for (const auto& child: children) {
        if (child)
            child->setLocations(tokenList, file, line, col);
    }
}

Token *clangimport::AstNode::addtoken(TokenList &tokenList, const std::string &str, bool valueType)
{
    const Scope *scope = getNestedInScope(tokenList);
    tokenList.addtoken(str, mLine, mCol, mFile);
    tokenList.back()->scope(scope);
    if (valueType)
        setValueType(tokenList.back());
    return tokenList.back();
}

Token *clangimport::AstNode::addtokenAtRange(TokenList &tokenList, const std::string &str, const char *where)
{
    const int file = mFile;
    const int line = mLine;
    const int col = mCol;
    if (const picojson::object *loc = getRangeLocation(mJsonObject, where))
        readLocation(tokenList, *loc, mFile, mLine, mCol);
    Token *tok = addtoken(tokenList, str, false);
    mFile = file;
    mLine = line;
    mCol = col;
    return tok;
}

const ::Type * clangimport::AstNode::addTypeTokens(TokenList &tokenList, const std::string &str0, const Scope *scope)
{
    // the type of a lambda is written "auto"
    const std::string str = startsWith(str0, "(lambda at ") ? std::string("auto") : mData.replaceAnonymousTypes(str0);
    if (str.find("(unnamed ") != std::string::npos)
        return nullptr;

    std::string type;
    if (str.find(" (") != std::string::npos) {
        if (str.find('<') != std::string::npos)
            type = str.substr(0, str.find('<') + 1) + "...>";
        else {
            type = str.substr(0, str.find(" ("));
            // function pointer "int (*)(int)" => "int *"
            if (str.compare(str.find(" (") + 1, 4, "(*)(") == 0)
                type += " *";
        }
    } else
        type = str;

    if (type.find("(*)(") != std::string::npos) {
        type.erase(type.find("(*)("));
        type += "*";
    }
    if (type.find('(') != std::string::npos)
        type.erase(type.find('('));

    // "unsigned long" => "long" with unsigned flag, same as the normal tokenizer.
    // simplifyStdType expects a name after the type so add a temporary one.
    TokenList typeTokens(mData.mSettings, tokenList.isCPP() ? Standards::Language::CPP : Standards::Language::C);
    for (const std::string &s: splitString(type))
        typeTokens.addtoken(s, 0, 0, 0);
    if (!typeTokens.front())
        return nullptr;
    typeTokens.addtoken("x", 0, 0, 0);
    typeTokens.simplifyStdType();

    std::stack<Token *> lpar;
    for (const Token *typeToken = typeTokens.front(); typeToken != typeTokens.back(); typeToken = typeToken->next()) {
        Token *tok = addtoken(tokenList, typeToken->str(), false);
        tok->isUnsigned(typeToken->isUnsigned());
        tok->isSigned(typeToken->isSigned());
        tok->isLong(typeToken->isLong());
        if (tok->str() == "(" || tok->str() == "[")
            lpar.push(tok);
        else if (tok->str() == ")" || tok->str() == "]") {
            Token::createMutualLinks(tok, lpar.top());
            lpar.pop();
        }
    }

    // Set Type
    if (!scope) {
        scope = tokenList.back() ? tokenList.back()->scope() : nullptr;
        if (!scope)
            return nullptr;
    }
    for (Token *typeToken = tokenList.back(); Token::Match(typeToken, "&|&&|*|%name%"); typeToken = typeToken->previous()) {
        if (!typeToken->isName())
            continue;
        const ::Type *recordType = scope->symdb().findVariableType(scope, typeToken);
        if (recordType) {
            typeToken->type(recordType);
            return recordType;
        }
    }
    return nullptr;
}

void clangimport::AstNode::addFullScopeNameTokens(TokenList &tokenList, const Scope *recordScope)
{
    if (!recordScope)
        return;
    std::list<const Scope *> scopes;
    while (recordScope && recordScope != tokenList.back()->scope() && !recordScope->isExecutable()) {
        scopes.push_front(recordScope);
        recordScope = recordScope->nestedIn;
    }
    for (const Scope *s: scopes) {
        if (!s->className.empty()) {
            addtoken(tokenList, s->className);
            addtoken(tokenList, "::");
        }
    }
}

Scope *clangimport::AstNode::getNestedInScope(TokenList &tokenList)
{
    if (!tokenList.back())
        return &mData.mSymbolDatabase().scopeList.front();
    if (tokenList.back()->str() == "}" && mData.mNotScope.find(tokenList.back()) == mData.mNotScope.end())
        return const_cast<Scope *>(tokenList.back()->scope()->nestedIn);
    return getTokenScope(tokenList.back());
}

void clangimport::AstNode::setValueType(Token *tok)
{
    setValueType(tok, getQualType());
}

/**
 * Array type => pointer type, same as the value type in the normal import:
 * "int[3]" => "int *", "int[2][2]" => "int * *", "int (*)[2]" => "int * *", "int (&)[2]" => "int *"
 */
static std::string arrayToPointerType(const std::string &type)
{
    const std::string::size_type pointerToArray = type.find("(*)[");
    const std::string::size_type referenceToArray = type.find("(&)[");
    const std::string::size_type pos = std::min(pointerToArray, referenceToArray);
    std::string::size_type dims = type.find('[');
    if (dims == std::string::npos || (type.find('(') != std::string::npos && pos == std::string::npos))
        return type;
    std::string ret = type.substr(0, pos != std::string::npos ? pos : dims);
    if (pointerToArray != std::string::npos)
        ret += " *";
    for (; dims != std::string::npos; dims = type.find('[', dims + 1))
        ret += " *";
    return ret;
}

void clangimport::AstNode::setValueType(Token *tok, const std::string &type0, const Scope *scope)
{
    const std::string type = arrayToPointerType(type0);
    if (type.find('<') != std::string::npos)
        // TODO
        return;

    TokenList decl(mData.mSettings, tok->isCpp() ? Standards::Language::CPP : Standards::Language::C);
    addTypeTokens(decl, type, scope ? scope : tok->scope());
    if (!decl.front())
        return;

    ValueType valueType = ValueType::parseDecl(decl.front(), mData.mSettings);
    if (valueType.type != ValueType::Type::UNKNOWN_TYPE)
        tok->setValueType(new ValueType(std::move(valueType)));
}

/** set the AST operands of op, returns op */
static Token *setAstOperands(Token *op, Token *op1, Token *op2)
{
    op->astOperand1(op1);
    op->astOperand2(op2);
    return op;
}

/** "public", "protected", "private" => AccessControl */
static AccessControl getAccessControl(const std::string &access)
{
    if (access == "private")
        return AccessControl::Private;
    if (access == "protected")
        return AccessControl::Protected;
    return AccessControl::Public;
}

/** "struct", "union", "class" => scope type */
static ScopeType getRecordScopeType(const std::string &tagUsed)
{
    if (tagUsed == "union")
        return ScopeType::eUnion;
    if (tagUsed == "class")
        return ScopeType::eClass;
    return ScopeType::eStruct;
}

void clangimport::AstNode::moveConditionVariables(const Token *def, Scope *scope)
{
    std::map<const Variable *, const Variable *> replaceVar;
    for (const Token *vartok = def->tokAt(2); vartok; vartok = vartok->next()) {
        if (!vartok->variable())
            continue;
        if (vartok->variable()->nameToken() == vartok) {
            const Variable *from = vartok->variable();
            scope->varlist.emplace_back(*from, scope);
            Variable *to = &scope->varlist.back();
            replaceVar[from] = to;
            mData.replaceVarDecl(from, to);
        }
        if (replaceVar.find(vartok->variable()) != replaceVar.end())
            const_cast<Token *>(vartok)->variable(replaceVar[vartok->variable()]);
    }
    std::list<Variable> &varlist = getTokenScope(def)->varlist;
    for (auto var = varlist.cbegin(); var != varlist.cend();) {
        if (replaceVar.find(&(*var)) != replaceVar.end())
            var = varlist.erase(var);
        else
            ++var;
    }
}

Scope *clangimport::AstNode::createScope(TokenList &tokenList, ScopeType scopeType, AstNodePtr astNode, const Token *def)
{
    std::vector<AstNodePtr> children2{std::move(astNode)};
    return createScope(tokenList, scopeType, children2, def);
}

Scope *clangimport::AstNode::createScope(TokenList &tokenList, ScopeType scopeType, const std::vector<AstNodePtr> & children2, const Token *def, Scope *existingScope)
{
    SymbolDatabase &symbolDatabase = mData.mSymbolDatabase;

    Scope *nestedIn = getNestedInScope(tokenList);

    Scope *scope = existingScope;
    if (!scope) {
        symbolDatabase.scopeList.emplace_back(nestedIn->symdb, nullptr, nestedIn);
        scope = &symbolDatabase.scopeList.back();
        nestedIn->nestedList.push_back(scope);
    }
    if (scopeType == ScopeType::eEnum)
        scope->enumeratorList.reserve(children2.size());
    scope->type = scopeType;
    scope->classDef = def; // TODO: pass into ctor
    if (!existingScope && scope->isClassOrStructOrUnion()) {
        // add the type before the body so it can be used in the member functions
        scope->className = def->strAt(1);
        symbolDatabase.typeList.emplace_back(def, scope, nestedIn);
        scope->definedType = &symbolDatabase.typeList.back();
        nestedIn->definedTypesMap[scope->className] = scope->definedType;
    }
    if (Token::Match(def, "if|for|while|catch ("))
        moveConditionVariables(def, scope);
    // location of braces: use the body statement for executable scopes "if (x) { .. }" / "if (x) y = 0;"
    const bool isBody = children2.size() == 1 && children2[0] && !Token::Match(def, "struct|class|union|enum|namespace");
    AstNode *braces = isBody ? children2[0].get() : this;
    Token *bodyStart;
    if (isBody && children2[0]->mKind != CompoundStmt && tokenList.back()) {
        // added braces "if (x) { y = 0; }": same location as the normal tokenizer
        const Token *prev = tokenList.back();
        bodyStart = addtoken(tokenList, "{", false);
        bodyStart->fileIndex(prev->fileIndex());
        bodyStart->linenr(prev->linenr());
        bodyStart->column(prev->column());
    } else {
        bodyStart = isBody ? braces->addtokenAtRange(tokenList, "{", "begin") : addtoken(tokenList, "{", false);
    }
    bodyStart->scope(scope);
    scope->bodyStart = bodyStart;
    if (scope->isClassOrStructOrUnion())
        mData.scopeAccessControl[scope] = scope->defaultAccess();
    for (const AstNodePtr &astNode: children2) {
        if (astNode->mKind == "VisibilityAttr")
            continue;
        if (astNode->mKind == AccessSpecDecl) {
            const std::string access = astNode->jsonString("access");
            // same as the normal tokenizer: "public:"
            astNode->addtoken(tokenList, access + ":");
            mData.scopeAccessControl[scope] = getAccessControl(access);
            continue;
        }
        astNode->createTokens(tokenList);
        if (scopeType == ScopeType::eEnum)
            astNode->addtoken(tokenList, ",");
        else if (!Token::Match(tokenList.back(), "[;{}]") || mData.mNotScope.count(tokenList.back()))
            astNode->addtokenAtRange(tokenList, ";", "end");
    }
    Token *bodyEnd = braces->addtokenAtRange(tokenList, "}", "end");
    Token::createMutualLinks(bodyStart, bodyEnd);
    scope->bodyEnd = bodyEnd;
    mData.scopeAccessControl.erase(scope);
    return scope;
}

Token *clangimport::AstNode::createTokens(TokenList &tokenList)
{
    // function that creates the tokens for each node kind
    using CreateTokens = Token *(AstNode::*)(TokenList &tokenList);
    static const std::unordered_map<std::string, CreateTokens> createTokensMap = {
        {ArraySubscriptExpr, &AstNode::createTokensArraySubscriptExpr},
        {BinaryOperator, &AstNode::createTokensBinaryOperator},
        {BreakStmt, &AstNode::createTokensKeyword},
        {CallExpr, &AstNode::createTokensCall},
        {CaseStmt, &AstNode::createTokensCaseStmt},
        {CharacterLiteral, &AstNode::createTokensCharacterLiteral},
        {ClassTemplateDecl, &AstNode::createTokensClassTemplateDecl},
        {ClassTemplateSpecializationDecl, &AstNode::createTokensRecord},
        {CompoundAssignOperator, &AstNode::createTokensBinaryOperator},
        {CompoundStmt, &AstNode::createTokensCompoundStmt},
        {ConditionalOperator, &AstNode::createTokensConditionalOperator},
        {ConstantExpr, &AstNode::createTokensFirstChild},
        {ContinueStmt, &AstNode::createTokensKeyword},
        {CStyleCastExpr, &AstNode::createTokensCStyleCastExpr},
        {CXXBindTemporaryExpr, &AstNode::createTokensFirstChild},
        {CXXBoolLiteralExpr, &AstNode::createTokensCXXBoolLiteralExpr},
        {CXXConstructExpr, &AstNode::createTokensCXXConstructExpr},
        {CXXConstructorDecl, &AstNode::createTokensFunction},
        {CXXDeleteExpr, &AstNode::createTokensCXXDeleteExpr},
        {CXXDestructorDecl, &AstNode::createTokensFunction},
        {CXXForRangeStmt, &AstNode::createTokensCXXForRangeStmt},
        {CXXCatchStmt, &AstNode::createTokensCXXCatchStmt},
        {CXXConstCastExpr, &AstNode::createTokensCXXNamedCastExpr},
        {CXXDynamicCastExpr, &AstNode::createTokensCXXNamedCastExpr},
        {CXXFunctionalCastExpr, &AstNode::createTokensCXXFunctionalCastExpr},
        {CXXMemberCallExpr, &AstNode::createTokensCall},
        {CXXMethodDecl, &AstNode::createTokensCXXMethodDecl},
        {CXXNewExpr, &AstNode::createTokensCXXNewExpr},
        {CXXNullPtrLiteralExpr, &AstNode::createTokensKeyword},
        {CXXOperatorCallExpr, &AstNode::createTokensCXXOperatorCallExpr},
        {CXXRecordDecl, &AstNode::createTokensRecord},
        {CXXReinterpretCastExpr, &AstNode::createTokensCXXNamedCastExpr},
        {CXXStaticCastExpr, &AstNode::createTokensCXXNamedCastExpr},
        {CXXStdInitializerListExpr, &AstNode::createTokensFirstChild},
        {CXXTemporaryObjectExpr, &AstNode::createTokensCXXTemporaryObjectExpr},
        {CXXThisExpr, &AstNode::createTokensKeyword},
        {CXXThrowExpr, &AstNode::createTokensCXXThrowExpr},
        {CXXTryStmt, &AstNode::createTokensCXXTryStmt},
        {DeclRefExpr, &AstNode::createTokensDeclRefExpr},
        {DeclStmt, &AstNode::createTokensDeclStmt},
        {DefaultStmt, &AstNode::createTokensDefaultStmt},
        {DoStmt, &AstNode::createTokensDoStmt},
        {EnumConstantDecl, &AstNode::createTokensEnumConstantDecl},
        {EnumDecl, &AstNode::createTokensEnumDecl},
        {ExprWithCleanups, &AstNode::createTokensFirstChild},
        {FieldDecl, &AstNode::createTokensVariable},
        {FloatingLiteral, &AstNode::createTokensFloatingLiteral},
        {ForStmt, &AstNode::createTokensForStmt},
        {FunctionDecl, &AstNode::createTokensFunction},
        {FunctionTemplateDecl, &AstNode::createTokensFunctionTemplateDecl},
        {GotoStmt, &AstNode::createTokensGotoStmt},
        {IfStmt, &AstNode::createTokensIfStmt},
        {ImplicitCastExpr, &AstNode::createTokensImplicitCastExpr},
        {InitListExpr, &AstNode::createTokensInitListExpr},
        {IntegerLiteral, &AstNode::createTokensValue},
        {LabelStmt, &AstNode::createTokensLabelStmt},
        {LambdaExpr, &AstNode::createTokensLambdaExpr},
        {LinkageSpecDecl, &AstNode::createTokensIgnored},
        {MaterializeTemporaryExpr, &AstNode::createTokensFirstChild},
        {MemberExpr, &AstNode::createTokensMemberExpr},
        {NamespaceDecl, &AstNode::createTokensNamespaceDecl},
        {NullStmt, &AstNode::createTokensKeyword},
        {ParenExpr, &AstNode::createTokensParenExpr},
        {ParmVarDecl, &AstNode::createTokensVariable},
        {RecordDecl, &AstNode::createTokensRecordDecl},
        {ReturnStmt, &AstNode::createTokensReturnStmt},
        {StringLiteral, &AstNode::createTokensValue},
        {SwitchStmt, &AstNode::createTokensSwitchStmt},
        {TypedefDecl, &AstNode::createTokensTypedefDecl},
        {UnaryExprOrTypeTraitExpr, &AstNode::createTokensUnaryExprOrTypeTraitExpr},
        {UnaryOperator, &AstNode::createTokensUnaryOperator},
        {UsingDirectiveDecl, &AstNode::createTokensUsingDirectiveDecl},
        {VarDecl, &AstNode::createTokensVariable},
        {WhileStmt, &AstNode::createTokensWhileStmt}
    };
    const auto it = createTokensMap.find(mKind);
    if (it != createTokensMap.end())
        return (this->*(it->second))(tokenList);
    // unknown node kind
    return addtoken(tokenList, "?" + mKind + "?");
}

// BreakStmt, ContinueStmt, CXXNullPtrLiteralExpr, CXXThisExpr, NullStmt
Token *clangimport::AstNode::createTokensKeyword(TokenList &tokenList)
{
    static const std::unordered_map<std::string, std::string> keywords = {
        {BreakStmt, "break"},
        {ContinueStmt, "continue"},
        {CXXNullPtrLiteralExpr, "nullptr"},
        {CXXThisExpr, "this"},
        {NullStmt, ";"}
    };
    return addtoken(tokenList, keywords.at(mKind));
}

// nodes that only wrap their child: ConstantExpr, ExprWithCleanups, ..
Token *clangimport::AstNode::createTokensFirstChild(TokenList &tokenList)
{
    return getChild(0)->createTokens(tokenList);
}

Token *clangimport::AstNode::createTokensCXXTemporaryObjectExpr(TokenList &tokenList)
{
    if (children.empty())
        return addtoken(tokenList, "?" + mKind + "?");
    return getChild(0)->createTokens(tokenList);
}

// IntegerLiteral, StringLiteral
Token *clangimport::AstNode::createTokensValue(TokenList &tokenList)
{
    return addtoken(tokenList, jsonString("value"));
}

// nodes that are not imported: LinkageSpecDecl
Token *clangimport::AstNode::createTokensIgnored(TokenList &tokenList)
{
    (void)tokenList;
    return nullptr;
}

// VarDecl, ParmVarDecl, FieldDecl
Token *clangimport::AstNode::createTokensVariable(TokenList &tokenList)
{
    return createTokensVarDecl(tokenList);
}

// FunctionDecl, CXXConstructorDecl, CXXDestructorDecl
Token *clangimport::AstNode::createTokensFunction(TokenList &tokenList)
{
    createTokensFunctionDecl(tokenList);
    return nullptr;
}

// CXXRecordDecl, ClassTemplateSpecializationDecl
Token *clangimport::AstNode::createTokensRecord(TokenList &tokenList)
{
    createTokensForCXXRecord(tokenList);
    return nullptr;
}

Token *clangimport::AstNode::createTokensArraySubscriptExpr(TokenList &tokenList)
{
    Token *array = getChild(0)->createTokens(tokenList);
    Token *bracket1 = addtoken(tokenList, "[");
    Token *index = children[1]->createTokens(tokenList);
    Token *bracket2 = addtoken(tokenList, "]");
    setAstOperands(bracket1, array, index);
    Token::createMutualLinks(bracket1, bracket2);
    return bracket1;
}

// BinaryOperator, CompoundAssignOperator
Token *clangimport::AstNode::createTokensBinaryOperator(TokenList &tokenList)
{
    // "a + b", "a += b"
    Token *tok1 = getChild(0)->createTokens(tokenList);
    Token *binop = addtoken(tokenList, getSpelling());
    Token *tok2 = children[1]->createTokens(tokenList);
    return setAstOperands(binop, tok1, tok2);
}

Token *clangimport::AstNode::createTokensCharacterLiteral(TokenList &tokenList)
{
    const int c = mJsonObject.at("value").get<int64_t>();
    if (c == 0)
        return addtoken(tokenList, "\'\\0\'");
    if (c == '\r')
        return addtoken(tokenList, "\'\\r\'");
    if (c == '\n')
        return addtoken(tokenList, "\'\\n\'");
    if (c == '\t')
        return addtoken(tokenList, "\'\\t\'");
    if (c == '\\')
        return addtoken(tokenList, "\'\\\\\'");
    if (c < ' ' || c >= 0x80) {
        std::ostringstream hex;
        hex << std::hex << ((c>>4) & 0xf) << (c&0xf);
        return addtoken(tokenList, "\'\\x" + hex.str() + "\'");
    }
    return addtoken(tokenList, std::string("\'") + char(c) + std::string("\'"));
}

Token *clangimport::AstNode::createTokensCaseStmt(TokenList &tokenList)
{
    Token *caseToken = addtoken(tokenList, "case");
    Token *exprToken = getChild(0)->createTokens(tokenList);
    caseToken->astOperand1(exprToken);
    addLabelColon(tokenList);
    createTokensStatement(tokenList, children.back());
    return nullptr;
}

Token *clangimport::AstNode::createTokensClassTemplateDecl(TokenList &tokenList)
{
    for (const AstNodePtr& child: children) {
        if (child->mKind == ClassTemplateSpecializationDecl)
            child->createTokens(tokenList);
    }
    return nullptr;
}

Token *clangimport::AstNode::createTokensConditionalOperator(TokenList &tokenList)
{
    Token *expr1 = getChild(0)->createTokens(tokenList);
    Token *tok1 = addtoken(tokenList, "?");
    Token *expr2 = children[1]->createTokens(tokenList);
    Token *tok2 = addtoken(tokenList, ":");
    Token *expr3 = children[2]->createTokens(tokenList);
    setAstOperands(tok2, expr2, expr3);
    return setAstOperands(tok1, expr1, tok2);
}

Token *clangimport::AstNode::createTokensCompoundStmt(TokenList &tokenList)
{
    for (const AstNodePtr& child: children) {
        createTokensStatement(tokenList, child);
        if (!Token::Match(tokenList.back(), "[;{}]"))
            child->addtokenAtRange(tokenList, ";", "end");
    }
    return nullptr;
}

Token *clangimport::AstNode::createTokensCStyleCastExpr(TokenList &tokenList)
{
    Token *par1 = addtoken(tokenList, "(");
    addTypeTokens(tokenList, getQualType());
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    par1->astOperand1(getChild(0)->createTokens(tokenList));
    return par1;
}

Token *clangimport::AstNode::createTokensCXXBoolLiteralExpr(TokenList &tokenList)
{
    addtoken(tokenList, jsonBool("value") ? "true" : "false");
    tokenList.back()->setValueType(new ValueType(ValueType::Sign::UNKNOWN_SIGN, ValueType::Type::BOOL, 0));
    return tokenList.back();
}

Token *clangimport::AstNode::createTokensCXXConstructExpr(TokenList &tokenList)
{
    if (!children.empty())
        return getChild(0)->createTokens(tokenList);
    addTypeTokens(tokenList, getQualType());
    Token *type = tokenList.back();
    Token *par1 = addtoken(tokenList, "(");
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    par1->astOperand1(type);
    return par1;
}

// "delete p", "delete [ ] p"
Token *clangimport::AstNode::createTokensCXXDeleteExpr(TokenList &tokenList)
{
    Token *deletetok = addtoken(tokenList, "delete", false);
    if (jsonBool("isArrayAsWritten")) {
        Token *bracket1 = addtoken(tokenList, "[", false);
        Token *bracket2 = addtoken(tokenList, "]", false);
        Token::createMutualLinks(bracket1, bracket2);
    }
    deletetok->astOperand1(getChild(0)->createTokens(tokenList));
    return deletetok;
}

Token *clangimport::AstNode::createTokensCXXForRangeStmt(TokenList &tokenList)
{
    Token *forToken = addtoken(tokenList, "for");
    Token *par1 = addtoken(tokenList, "(");
    AstNodePtr varDecl;
    for (auto it = children.rbegin(); it != children.rend(); ++it) {
        if ((*it)->mKind == DeclStmt) {
            varDecl = (*it)->getChild(0);
            break;
        }
    }
    varDecl->children.clear();
    Token *expr1 = varDecl->createTokens(tokenList);
    Token *colon = addtoken(tokenList, ":");
    AstNodePtr range;
    for (std::size_t i = 0; i < 2; i++) {
        if (children[i] && children[i]->mKind == DeclStmt && children[i]->getChild(0)->mKind == VarDecl) {
            range = children[i]->getChild(0)->getChild(0);
            break;
        }
    }
    if (!range)
        throw InternalError(tokenList.back(), "Failed to import CXXForRangeStmt. Range?");
    Token *expr2 = range->createTokens(tokenList);
    Token *par2 = addtoken(tokenList, ")");

    Token::createMutualLinks(par1, par2);

    setAstOperands(colon, expr1, expr2);
    setAstOperands(par1, forToken, colon);

    createScope(tokenList, ScopeType::eFor, children.back(), forToken);

    return nullptr;
}

Token *clangimport::AstNode::createTokensCXXMethodDecl(TokenList &tokenList)
{
    // out of line definition of a template member function "template<class T> void A<T>::f() {}":
    // the class template is not imported, only the instantiations.
    const std::string prev = jsonString("previousDecl");
    if (!prev.empty() && !mData.hasDecl(prev))
        return nullptr;
    createTokensFunctionDecl(tokenList);
    return nullptr;
}

// "new T", "new T [ n ]", "new T ( args )", "new T { args }", "new T [ n ] { args }"
Token *clangimport::AstNode::createTokensCXXNewExpr(TokenList &tokenList)
{
    Token *newtok = addtoken(tokenList, "new");

    // the type of the expression is "T *"
    std::string type = getQualType();
    if (type.find('*') != std::string::npos)
        type.erase(type.rfind('*'));
    addTypeTokens(tokenList, type);
    Token *expr = tokenList.back();

    // children: array size, initializer
    std::size_t child = 0;
    if (jsonBool("isArray") && child < children.size()) {
        Token *bracket1 = addtoken(tokenList, "[", false);
        Token *size = children[child++]->createTokens(tokenList);
        Token *bracket2 = addtoken(tokenList, "]", false);
        Token::createMutualLinks(bracket1, bracket2);
        expr = setAstOperands(bracket1, expr, size);
    }

    // initializer that is written in the code. Without "initStyle" it is a call of the default constructor that clang adds.
    if (!jsonString("initStyle").empty() && child < children.size()) {
        const AstNodePtr &init = children[child];
        Token *par1 = init->createTokensInitArgs(tokenList, expr);
        if (par1->str() == "(")
            init->setValueType(par1);
        expr = par1;
    }

    newtok->astOperand1(expr);
    return newtok;
}

// "static_cast < T > ( expr )", also reinterpret_cast, const_cast, dynamic_cast
Token *clangimport::AstNode::createTokensCXXNamedCastExpr(TokenList &tokenList)
{
    static const std::unordered_map<std::string, std::string> keywords = {
        {CXXConstCastExpr, "const_cast"},
        {CXXDynamicCastExpr, "dynamic_cast"},
        {CXXReinterpretCastExpr, "reinterpret_cast"},
        {CXXStaticCastExpr, "static_cast"}
    };
    Token *cast = addtoken(tokenList, keywords.at(mKind), false);
    Token *lt = addtoken(tokenList, "<", false);
    addTypeTokens(tokenList, getQualType());
    Token *gt = addtoken(tokenList, ">", false);
    Token::createMutualLinks(lt, gt);
    Token *par1 = addtoken(tokenList, "(", false);
    Token *expr = getChild(0)->createTokens(tokenList);
    Token *par2 = addtoken(tokenList, ")", false);
    Token::createMutualLinks(par1, par2);
    setAstOperands(par1, cast, expr);
    setValueType(par1);
    return par1;
}

// "T ( expr )", "T { expr }"
Token *clangimport::AstNode::createTokensCXXFunctionalCastExpr(TokenList &tokenList)
{
    addTypeTokens(tokenList, getQualType());
    Token *par1 = getChild(0)->createTokensInitArgs(tokenList, tokenList.back());
    setValueType(par1);
    return par1;
}

// "throw x", "throw"
Token *clangimport::AstNode::createTokensCXXThrowExpr(TokenList &tokenList)
{
    Token *t = addtoken(tokenList, "throw", false);
    if (!children.empty())
        t->astOperand1(getChild(0)->createTokens(tokenList));
    return t;
}

// "try { .. } catch ( .. ) { .. }"
Token *clangimport::AstNode::createTokensCXXTryStmt(TokenList &tokenList)
{
    Token *tryToken = addtoken(tokenList, "try");
    createScope(tokenList, ScopeType::eTry, getChild(0), tryToken);
    for (std::size_t i = 1; i < children.size(); ++i)
        children[i]->createTokens(tokenList);
    return nullptr;
}

// "catch ( int e ) { .. }", "catch ( ... ) { .. }". The exception declaration is null for "...".
Token *clangimport::AstNode::createTokensCXXCatchStmt(TokenList &tokenList)
{
    Token *catchToken = addtoken(tokenList, "catch");
    Token *par1 = addtoken(tokenList, "(");
    Token *decl = children[0] ? children[0]->createTokens(tokenList) : addtoken(tokenList, "...");
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    setAstOperands(par1, catchToken, decl);
    createScope(tokenList, ScopeType::eCatch, children.back(), catchToken);
    return nullptr;
}

Token *clangimport::AstNode::createTokensDeclRefExpr(TokenList &tokenList)
{
    const picojson::object &referencedDecl = mJsonObject.at("referencedDecl").get<picojson::object>();
    const std::string addr = getJsonString(referencedDecl, "id");
    std::string name = getJsonString(referencedDecl, "name");
    // clang does not write the qualification "N::" => add it if the declaration is not visible
    std::vector<const Scope *> qualifiers;
    const Scope *currentScope = getNestedInScope(tokenList);
    const Scope *declScope = mData.getDeclScope(addr);
    // local variables and parameters are never qualified
    if (declScope && declScope->isExecutable())
        declScope = nullptr;
    for (const Scope *s = declScope; s && !isVisibleScope(s, currentScope); s = s->nestedIn) {
        if (!s->className.empty())
            qualifiers.insert(qualifiers.begin(), s);
    }
    Token *qualified = nullptr;
    Token *colon = nullptr;
    for (const Scope *s: qualifiers) {
        Token *nameToken = addtoken(tokenList, s->className, false);
        qualified = colon ? setAstOperands(colon, qualified, nameToken) : nameToken;
        colon = addtoken(tokenList, "::", false);
    }
    Token *reftok = addtoken(tokenList, name.empty() ? "<NoName>" : std::move(name));
    mData.ref(addr, reftok);
    if (colon) {
        setAstOperands(colon, qualified, reftok);
        setValueType(colon);
        return colon;
    }
    return reftok;
}

Token *clangimport::AstNode::createTokensDeclStmt(TokenList &tokenList)
{
    // declarations in for loop: "for (int i = 0, *p = &i;" => "i = 0 , * p = & i"
    Token *expr = getChild(0)->createTokens(tokenList);
    const Token *vartok1 = Token::simpleMatch(expr, "=") ? expr->astOperand1() : expr;
    const Variable *var1 = vartok1 ? vartok1->variable() : nullptr;
    if (!var1)
        return expr;
    std::string baseType = getQualTypeBefore(getChild(0)->getQualType());
    baseType = baseType.substr(0, baseType.find_first_of("*&("));
    while (endsWith(baseType, ' '))
        baseType.pop_back();
    const Token *baseTypeEnd = var1->typeStartToken();
    while (baseTypeEnd->next() != var1->nameToken() && !Token::Match(baseTypeEnd->next(), "*|&|&&"))
        baseTypeEnd = baseTypeEnd->next();
    for (std::size_t i = 1; i < children.size(); ++i) {
        const AstNodePtr &decl = children[i];
        if (decl->mKind != VarDecl || !startsWith(decl->getQualType(), baseType))
            break;
        Token *comma = addtoken(tokenList, ",", false);
        setAstOperands(comma, expr, decl->createTokensVarDecl(tokenList, var1, baseTypeEnd, baseType));
        expr = comma;
    }
    return expr;
}

Token *clangimport::AstNode::createTokensDefaultStmt(TokenList &tokenList)
{
    addtoken(tokenList, "default");
    addLabelColon(tokenList);
    createTokensStatement(tokenList, children.back());
    return nullptr;
}

Token *clangimport::AstNode::createTokensDoStmt(TokenList &tokenList)
{
    addtoken(tokenList, "do");
    createScope(tokenList, ScopeType::eDo, getChild(0), tokenList.back());
    Token *whiletok = addtoken(tokenList, "while");
    createTokensCondition(tokenList, whiletok, children[1]);
    return nullptr;
}

Token *clangimport::AstNode::createTokensEnumConstantDecl(TokenList &tokenList)
{
    const std::string name = getSpelling();
    if (name.empty())
        throw InternalError(nullptr, "invalid AST node: " + mKind, InternalError::AST);
    Token *nameToken = addtoken(tokenList, name);
    auto *scope = getTokenScope(nameToken);
    scope->enumeratorList.emplace_back(nameToken->scope());
    Enumerator *e = &scope->enumeratorList.back();
    e->name = nameToken;
    e->value_known = true;
    if (!children.empty()) {
        // explicit value
        Token *eq = addtoken(tokenList, "=", false);
        const AstNodePtr valueExpr = getChild(0);
        setAstOperands(eq, nameToken, valueExpr->createTokens(tokenList));
        e->start = eq->next();
        e->end = tokenList.back();
        // clang has calculated the value, in C++ it is wrapped in a implicit cast
        AstNodePtr constantExpr = valueExpr;
        while (constantExpr->mKind == ImplicitCastExpr && !constantExpr->children.empty())
            constantExpr = constantExpr->getChild(0);
        if (constantExpr->mKind == ConstantExpr && constantExpr->mJsonObject.count("value"))
            mData.enumValue = MathLib::toBigNumber(constantExpr->jsonString("value"));
        else
            e->value_known = false;
    }
    e->value = mData.enumValue++;
    mData.enumDecl(getId(), nameToken, e);
    return nameToken;
}

Token *clangimport::AstNode::createTokensEnumDecl(TokenList &tokenList)
{
    mData.enumValue = 0;
    Token *enumtok = addtoken(tokenList, "enum");
    // enum class / enum struct
    const std::string scopedEnumTag = jsonString("scopedEnumTag");
    if (!scopedEnumTag.empty())
        addtoken(tokenList, scopedEnumTag);
    const Token *nametok = addtoken(tokenList, getTypeName(tokenList));
    Token *enumType = nullptr;
    if (mJsonObject.count("fixedUnderlyingType")) {
        addtoken(tokenList, ":");
        addTypeTokens(tokenList, getJsonQualType(mJsonObject, "fixedUnderlyingType"));
        enumType = tokenList.back();
    }
    Scope *enumscope = createScope(tokenList, ScopeType::eEnum, children, enumtok);
    enumscope->enumClass = !scopedEnumTag.empty();
    enumscope->enumType = enumType;
    if (nametok)
        enumscope->className = nametok->str();
    if (enumscope->bodyEnd && Token::simpleMatch(enumscope->bodyEnd->previous(), ", }"))
        const_cast<Token *>(enumscope->bodyEnd)->deletePrevious();

    // Create enum type
    mData.mSymbolDatabase().typeList.emplace_back(enumtok, enumscope, enumtok->scope());
    enumscope->definedType = &mData.mSymbolDatabase().typeList.back();
    if (nametok)
        getTokenScope(enumtok)->definedTypesMap[nametok->str()] = enumscope->definedType;

    addtokenAtRange(tokenList, ";", "end");
    return nullptr;
}

Token *clangimport::AstNode::createTokensFloatingLiteral(TokenList &tokenList)
{
    std::string value = jsonString("value");
    // clang writes 2.0 as "2", the token must be a floating point number
    if (value.find_first_not_of("0123456789") == std::string::npos)
        value += ".0";
    return addtoken(tokenList, value);
}

Token *clangimport::AstNode::createTokensForStmt(TokenList &tokenList)
{
    Token *forToken = addtoken(tokenList, "for");
    Token *par1 = addtoken(tokenList, "(");
    Token *expr1 = getChild(0) ? children[0]->createTokens(tokenList) : nullptr;
    Token *sep1 = addtoken(tokenList, ";");
    Token *expr2 = children[2] ? children[2]->createTokens(tokenList) : nullptr;
    Token *sep2 = addtoken(tokenList, ";");
    Token *expr3 = children[3] ? children[3]->createTokens(tokenList) : nullptr;
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    setAstOperands(par1, forToken, sep1);
    setAstOperands(sep1, expr1, sep2);
    setAstOperands(sep2, expr2, expr3);
    createScope(tokenList, ScopeType::eFor, children[4], forToken);
    return nullptr;
}

Token *clangimport::AstNode::createTokensFunctionTemplateDecl(TokenList &tokenList)
{
    bool first = true;
    for (const AstNodePtr& child: children) {
        if (child->mKind == FunctionDecl) {
            if (!first)
                child->createTokens(tokenList);
            first = false;
        }
    }
    return nullptr;
}

Token *clangimport::AstNode::createTokensGotoStmt(TokenList &tokenList)
{
    addtoken(tokenList, "goto");
    const auto it = mData.mLabelNames.find(jsonString("targetLabelDeclId"));
    if (it != mData.mLabelNames.end())
        addtoken(tokenList, it->second);
    addtoken(tokenList, ";");
    return nullptr;
}

Token *clangimport::AstNode::createTokensIfStmt(TokenList &tokenList)
{
    AstNodePtr cond;
    AstNodePtr thenCode;
    AstNodePtr elseCode;
    if (children.size() == 2) {
        cond = children[children.size() - 2];
        thenCode = children[children.size() - 1];
    } else {
        cond = children[children.size() - 3];
        thenCode = children[children.size() - 2];
        elseCode = children[children.size() - 1];
    }

    Token *iftok = addtoken(tokenList, "if");
    createTokensCondition(tokenList, iftok, cond);
    createScope(tokenList, ScopeType::eIf, std::move(thenCode), iftok);
    if (elseCode) {
        elseCode->addtoken(tokenList, "else");
        createScope(tokenList, ScopeType::eElse, std::move(elseCode), tokenList.back());
    }
    return nullptr;
}

Token *clangimport::AstNode::createTokensImplicitCastExpr(TokenList &tokenList)
{
    Token *expr = getChild(0)->createTokens(tokenList);
    // the type after the cast: array => pointer
    // a function name has no value type
    if ((!expr->valueType() && !expr->function()) || jsonString("castKind") == "ArrayToPointerDecay")
        setValueType(expr);
    return expr;
}

Token *clangimport::AstNode::createTokensInitListExpr(TokenList &tokenList)
{
    const Scope *scope = tokenList.back()->scope();
    Token *start = addtoken(tokenList, "{", false);
    start->scope(scope);
    // AST: the elements "a , b , c" are the operand of "{"
    Token *elements = nullptr;
    for (const AstNodePtr& child: children) {
        if (child->isImplicitInit())
            continue;
        Token *comma = elements ? addtoken(tokenList, ",", false) : nullptr;
        Token *element = child->createTokens(tokenList);
        elements = comma ? setAstOperands(comma, elements, element) : element;
    }
    start->astOperand1(elements);
    Token *end = addtoken(tokenList, "}");
    end->scope(scope);
    Token::createMutualLinks(start, end);
    mData.mNotScope.insert(end);
    return start;
}

Token *clangimport::AstNode::createTokensLabelStmt(TokenList &tokenList)
{
    addtoken(tokenList, getSpelling());
    addLabelColon(tokenList);
    for (const auto& child: children)
        createTokensStatement(tokenList, child);
    return nullptr;
}

Token *clangimport::AstNode::createTokensMemberExpr(TokenList &tokenList)
{
    // implicit "this->x" => write "x" like in the code
    if (getChild(0)->mKind == CXXThisExpr && getChild(0)->jsonBool("implicit")) {
        Token *member = addtoken(tokenList, jsonString("name"));
        if (mJsonObject.count("referencedMemberDecl"))
            mData.ref(jsonString("referencedMemberDecl"), member);
        return member;
    }
    Token *s = getChild(0)->createTokens(tokenList);
    Token *dot = addtoken(tokenList, ".");
    std::string memberName = getSpelling();
    if (startsWith(memberName, "->")) {
        dot->originalName("->");
        memberName = memberName.substr(2);
    } else if (startsWith(memberName, ".")) {
        memberName = memberName.substr(1);
    }
    if (memberName.empty())
        memberName = "<unknown>";
    // the member name is the last token of the expression
    Token *member = addtokenAtRange(tokenList, memberName, "end");
    setValueType(member);
    if (mJsonObject.count("referencedMemberDecl")) {
        // "this->x" refers to the member declaration
        mData.ref(jsonString("referencedMemberDecl"), member);
        // "s.x" gets its own varid
        const Token *object = (s && s->str() == "." && s->astOperand2()) ? s->astOperand2() : s;
        if (getChild(0)->mKind != CXXThisExpr && object && object->varId() && member->variable())
            member->varId(mData.memberVarId(object->varId(), member->variable()));
    }
    return setAstOperands(dot, s, member);
}

Token *clangimport::AstNode::createTokensNamespaceDecl(TokenList &tokenList)
{
    if (children.empty())
        return nullptr;
    const Token *defToken = addtoken(tokenList, "namespace");
    const std::string name = getSpelling();
    if (!name.empty())
        addtoken(tokenList, name);
    // reopened namespace => use the same scope
    Scope *previousScope = nullptr;
    if (mJsonObject.count("previousDecl"))
        previousScope = mData.getScope(jsonString("previousDecl"));
    Scope *scope = createScope(tokenList, ScopeType::eNamespace, children, defToken, previousScope);
    scope->className = name;
    mData.scopeDecl(getId(), scope);
    return nullptr;
}

Token *clangimport::AstNode::createTokensUsingDirectiveDecl(TokenList &tokenList)
{
    // clang adds "using namespace" for anonymous namespaces
    if (isImplicit())
        return nullptr;
    Token *usingToken = addtoken(tokenList, "using");
    addtoken(tokenList, "namespace");
    const picojson::object &ns = mJsonObject.at("nominatedNamespace").get<picojson::object>();
    addtoken(tokenList, getJsonString(ns, "name"));
    Scope::UsingInfo usingInfo;
    usingInfo.start = usingToken;
    usingInfo.scope = mData.getScope(getJsonString(ns, "id"));
    getTokenScope(usingToken)->usingList.push_back(usingInfo);
    return addtokenAtRange(tokenList, ";", "end");
}

Token *clangimport::AstNode::createTokensParenExpr(TokenList &tokenList)
{
    Token *par1 = addtoken(tokenList, "(");
    Token *expr = getChild(0)->createTokens(tokenList);
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    return expr;
}

Token *clangimport::AstNode::createTokensRecordDecl(TokenList &tokenList)
{
    const std::string tagUsed = jsonString("tagUsed", "struct");
    const Token *classDef = addtoken(tokenList, tagUsed);
    const std::string recordName = getTypeName(tokenList);
    if (!recordName.empty())
        addtoken(tokenList, recordName);
    if (!isDefinition()) {
        addtoken(tokenList, ";");
        return nullptr;
    }

    createScope(tokenList, getRecordScopeType(tagUsed), children, classDef);
    addtokenAtRange(tokenList, ";", "end");
    return nullptr;
}

Token *clangimport::AstNode::createTokensReturnStmt(TokenList &tokenList)
{
    Token *tok1 = addtoken(tokenList, "return");
    if (!children.empty()) {
        getChild(0)->setValueType(tok1);
        tok1->astOperand1(getChild(0)->createTokens(tokenList));
    }
    return tok1;
}

Token *clangimport::AstNode::createTokensSwitchStmt(TokenList &tokenList)
{
    Token *switchtok = addtoken(tokenList, "switch");
    createTokensCondition(tokenList, switchtok, children[children.size() - 2]);
    createScope(tokenList, ScopeType::eSwitch, children.back(), switchtok);
    return nullptr;
}

Token *clangimport::AstNode::createTokensTypedefDecl(TokenList &tokenList)
{
    addtoken(tokenList, "typedef");
    addTypeTokens(tokenList, getQualType());
    return addtoken(tokenList, getSpelling());
}

Token *clangimport::AstNode::createTokensUnaryOperator(TokenList &tokenList)
{
    const std::string& spelling = getSpelling();
    const bool postfix = jsonBool("isPostfix");
    if (postfix) {
        Token* tok = getChild(0)->createTokens(tokenList);
        Token *unaryOp = addtoken(tokenList, spelling);
        setValueType(unaryOp);
        unaryOp->astOperand1(tok);
        return unaryOp;
    } else {
        Token *unaryOp = addtoken(tokenList, spelling);
        setValueType(unaryOp);
        unaryOp->astOperand1(getChild(0)->createTokens(tokenList));
        return unaryOp;
    }
}

// "sizeof ( type )", "sizeof ( expr )"
Token *clangimport::AstNode::createTokensUnaryExprOrTypeTraitExpr(TokenList &tokenList)
{
    Token *tok1 = addtoken(tokenList, getSpelling(), false);
    Token *par1 = addtoken(tokenList, "(");
    Token *operand;
    if (children.empty()) {
        // sizeof(type)
        const std::string argType = getJsonQualType(mJsonObject, "argType");
        addTypeTokens(tokenList, argType);
        operand = tokenList.back();
        setValueType(operand, argType);
    } else {
        AstNodePtr child = getChild(0);
        if (child && child->mKind == ParenExpr)
            child = child->getChild(0);
        operand = child->createTokens(tokenList);
        child->setValueType(operand);
    }
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    setAstOperands(par1, tok1, operand);
    setValueType(par1);
    return par1;
}

Token *clangimport::AstNode::createTokensWhileStmt(TokenList &tokenList)
{
    AstNodePtr cond = children[children.size() - 2];
    AstNodePtr body = children.back();
    Token *whiletok = addtoken(tokenList, "while");
    createTokensCondition(tokenList, whiletok, cond);
    createScope(tokenList, ScopeType::eWhile, std::move(body), whiletok);
    return nullptr;
}

Token *clangimport::AstNode::createTokensCondition(TokenList &tokenList, Token *keyword, const AstNodePtr &cond)
{
    Token *par1 = addtoken(tokenList, "(");
    Token *expr = cond->createTokens(tokenList);
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    return setAstOperands(par1, keyword, expr);
}

void clangimport::AstNode::createTokensStatement(TokenList &tokenList, const AstNodePtr &stmt)
{
    if (stmt->mKind == CompoundStmt) {
        // block statement "{ ... }"
        Scope *scope = stmt->createScope(tokenList, ScopeType::eUnconditional, stmt, nullptr);
        scope->classDef = scope->bodyStart;
    } else if (stmt->mKind == DeclStmt) {
        // "int a, b;" => "int a ; int b ;"
        for (const AstNodePtr &decl: stmt->children) {
            if (decl->mKind == TypedefDecl)
                continue;
            decl->createTokens(tokenList);
            if (tokenList.back()->str() != ";")
                decl->addtokenAtRange(tokenList, ";", "end");
        }
    } else {
        stmt->createTokens(tokenList);
    }
}

// function call "f ( args )"
Token * clangimport::AstNode::createTokensCall(TokenList &tokenList)
{
    Token *f = getChild(0)->createTokens(tokenList);
    return createTokensCallArguments(tokenList, f, 1);
}

// "( args )" of a call, the arguments are children[firstArg..]
Token *clangimport::AstNode::createTokensCallArguments(TokenList &tokenList, Token *f, std::size_t firstArg)
{
    // the called function has no value type, a function pointer variable has
    if (!f->variable())
        f->setValueType(nullptr);
    Token *par1 = addtoken(tokenList, "(");
    par1->astOperand1(f);
    std::size_t args = 0;
    while (args < children.size() && children[args]->mKind != CXXDefaultArgExpr)
        args++;
    Token *child = nullptr;
    for (std::size_t c = firstArg; c < args; ++c) {
        Token *comma = child ? addtoken(tokenList, ",", false) : nullptr;
        Token *argTok = children[c]->createTokens(tokenList);
        child = comma ? setAstOperands(comma, child, argTok) : argTok;
    }
    par1->astOperand2(child);
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    return par1;
}

// overloaded operator, written like the normal import: "a + b", "! a", "a ++", "a [ i ]", "a . operator() ( args )"
Token *clangimport::AstNode::createTokensCXXOperatorCallExpr(TokenList &tokenList)
{
    // the operator function is the first child, the operands follow
    const AstNode *callee = getChild(0).get();
    while (callee->mKind == ImplicitCastExpr && !callee->children.empty())
        callee = callee->children[0].get();
    const picojson::object *decl = findJsonObject(callee->mJsonObject, "referencedDecl");
    const std::string name = decl ? getJsonString(*decl, "name") : "";
    const std::string op = startsWith(name, "operator") ? name.substr(8) : "";
    const std::size_t operands = children.size() - 1;

    if (op == "[]" && operands == 2) {
        Token *obj = getChild(1)->createTokens(tokenList);
        Token *bracket1 = addtoken(tokenList, "[");
        Token *index = getChild(2)->createTokens(tokenList);
        Token *bracket2 = addtoken(tokenList, "]", false);
        Token::createMutualLinks(bracket1, bracket2);
        return setAstOperands(bracket1, obj, index);
    }
    const bool isOperator = !op.empty() && op != "()" && op != "->" && std::isalpha(static_cast<unsigned char>(op[0])) == 0;
    if (isOperator && operands == 2 && (op == "++" || op == "--")) {
        // postfix, the second operand is a dummy int
        Token *operand = getChild(1)->createTokens(tokenList);
        Token *opTok = addtoken(tokenList, op);
        opTok->astOperand1(operand);
        return opTok;
    }
    if (isOperator && operands == 2) {
        Token *lhs = getChild(1)->createTokens(tokenList);
        Token *opTok = addtoken(tokenList, op);
        Token *rhs = getChild(2)->createTokens(tokenList);
        return setAstOperands(opTok, lhs, rhs);
    }
    if (isOperator && operands == 1) {
        Token *opTok = addtoken(tokenList, op);
        opTok->astOperand1(getChild(1)->createTokens(tokenList));
        return opTok;
    }

    // call of lambda "f ( args )"
    if (op == "()" && getChild(1)->getQualType().find("(lambda at ") != std::string::npos) {
        Token *f = getChild(1)->createTokens(tokenList);
        return createTokensCallArguments(tokenList, f, 2);
    }

    // "a . operator() ( args )"
    Token *obj = getChild(1)->createTokens(tokenList);
    Token *dot = addtoken(tokenList, ".", false);
    Token *opTok = addtoken(tokenList, name.empty() ? "operator" : name, false);
    if (decl)
        mData.ref(getJsonString(*decl, "id"), opTok);
    setAstOperands(dot, obj, opTok);
    return createTokensCallArguments(tokenList, dot, 2);
}

// "( args )" or "{ args }" of a direct initialization of "name"
Token *clangimport::AstNode::createTokensInitArgs(TokenList &tokenList, Token *name)
{
    std::vector<AstNode *> args;
    const bool isConstruct = mKind == CXXConstructExpr;
    if (isConstruct || mKind == InitListExpr) {
        for (const AstNodePtr &arg: children) {
            if (!arg->isImplicitInit())
                args.push_back(arg.get());
        }
    } else if (mKind != ImplicitValueInitExpr) {
        args.push_back(this);
    }
    const bool braces = mKind == InitListExpr ||
                        (isConstruct && jsonBool("list"));
    Token *par1 = addtoken(tokenList, braces ? "{" : "(", false);
    Token *argsAst = nullptr;
    for (AstNode *arg: args) {
        Token *comma = argsAst ? arg->addtoken(tokenList, ",", false) : nullptr;
        Token *argTok = arg->createTokens(tokenList);
        argsAst = comma ? setAstOperands(comma, argsAst, argTok) : argTok;
    }
    Token *par2 = addtokenAtRange(tokenList, braces ? "}" : ")", "end");
    if (braces)
        mData.mNotScope.insert(par2);
    Token::createMutualLinks(par1, par2);
    return setAstOperands(par1, name, argsAst);
}

void clangimport::AstNode::createTokensCtorInitializers(TokenList &tokenList)
{
    const int64_t ctorOffset = getLocationOffset(findJsonObject(mJsonObject, "loc"));
    bool first = true;
    for (const AstNodePtr &init: children) {
        if (init->mKind != CXXCtorInitializer || init->children.empty())
            continue;
        const AstNodePtr &expr = init->children[0];
        // skip initializers that clang adds: default member initializers, default constructors
        if (expr->mKind == CXXDefaultInitExpr)
            continue;
        if (expr->mKind == CXXConstructExpr && expr->children.empty() && getLocationOffset(getRangeLocation(expr->mJsonObject, "begin")) == ctorOffset)
            continue;

        expr->addtoken(tokenList, first ? ":" : ",");
        first = false;

        // name of member/base
        Token *name;
        if (init->mJsonObject.count("anyInit")) {
            const picojson::object &field = init->mJsonObject.at("anyInit").get<picojson::object>();
            name = expr->addtoken(tokenList, getJsonString(field, "name"), false);
            mData.ref(getJsonString(field, "id"), name);
            setValueType(name, getJsonQualType(field, "type"));
        } else {
            const char *key = init->mJsonObject.count("baseInit") ? "baseInit" : "delegatingInit";
            if (init->mJsonObject.count(key) == 0)
                continue;
            expr->addTypeTokens(tokenList, getJsonQualType(init->mJsonObject, key));
            name = tokenList.back();
        }

        expr->createTokensInitArgs(tokenList, name);
    }
}

void clangimport::AstNode::createTokensFunctionDecl(TokenList &tokenList)
{
    // an address-only node has no name: addtoken("") adds nothing and would return a null back()
    const std::string name = getSpelling();
    if (name.empty())
        throw InternalError(nullptr, "invalid AST node: " + mKind, InternalError::AST);
    const std::string prev = jsonString("previousDecl");
    // "= default", "= delete"
    const bool isDefault = jsonString("explicitlyDefaulted") == "default";
    const bool isDelete = jsonBool("explicitlyDeleted");
    // clang adds a body for "S::S() = default;"
    const bool hasBody = !isDefault && !isDelete && !children.empty() && children.back()->mKind == CompoundStmt;
    // out of line member function "void S::f() {}" => S
    const Scope* parentDeclContext = mJsonObject.count("parentDeclContextId") > 0 ?
                                     mData.getScope(jsonString("parentDeclContextId"))
                                     : nullptr;

    // specifiers, override/final are attributes
    const bool isVirtual = jsonBool("virtual");
    const bool isPure = jsonBool("pure");
    const bool isOverride = std::any_of(children.cbegin(), children.cend(), [](const AstNodePtr &child) {
        return child && child->mKind == "OverrideAttr";
    });
    const bool isFinal = std::any_of(children.cbegin(), children.cend(), [](const AstNodePtr &child) {
        return child && child->mKind == "FinalAttr";
    });
    if (isVirtual)
        addtoken(tokenList, "virtual");

    // storage class and return type
    Token *retDef = nullptr;
    if (mKind != CXXConstructorDecl && mKind != CXXDestructorDecl) {
        const std::string storageClass = getStorageClass();
        if (storageClass == "static" || storageClass == "extern")
            addtoken(tokenList, storageClass);
        Token * const before = tokenList.back();
        addTypeTokens(tokenList, getQualType());
        retDef = before ? before->next() : tokenList.front();
    }

    // name
    if (parentDeclContext)
        addFullScopeNameTokens(tokenList, parentDeclContext);
    // destructor "~ S" like the normal tokenizer
    if (mKind == CXXDestructorDecl)
        addtoken(tokenList, "~");
    Token *nameToken = addtoken(tokenList, (mKind == CXXDestructorDecl ? name.substr(1) : name) + getTemplateParameters());
    auto *nestedIn = getTokenScope(nameToken);

    // the normal tokenizer removes "inline" and sets a flag on the following names
    if (jsonBool("inline")) {
        for (Token *tok = retDef ? retDef : nameToken; Token::Match(tok, "%name%"); tok = tok->next())
            tok->isInline(true);
    }

    Function * const function = getFunction(tokenList, nameToken, retDef, prev);

    // body at the first declaration => inline
    if (prev.empty())
        function->clangSetFlags(hasBody, isDefault, isDelete);
    else if (isDefault || isDelete)
        function->clangSetFlags(function->isInline(), isDefault, isDelete);
    if (prev.empty())
        function->clangSetSpecifiers(isVirtual, isPure, isOverride, isFinal);

    Scope *scope = hasBody ? createFunctionScope(function, nameToken, parentDeclContext) : nullptr;

    // arguments
    // definition after declaration => the arguments are declared by the definition
    const bool declareArgs = prev.empty() || hasBody;
    Token *par1 = createTokensFunctionArguments(tokenList, function, scope, parentDeclContext ? parentDeclContext : nestedIn, declareArgs, prev.empty());
    // argDef: declaration, arg: definition
    if (prev.empty())
        function->argDef = par1;
    if (declareArgs)
        function->arg = par1;
    function->token = nameToken;
    if (!function->nestedIn)
        function->nestedIn = nestedIn;

    if (function->isConst())
        addtoken(tokenList, "const");
    if (isOverride)
        addtoken(tokenList, "override");
    if (isFinal)
        addtoken(tokenList, "final");

    if (mKind == CXXConstructorDecl && hasBody)
        createTokensCtorInitializers(tokenList);

    if (hasBody) {
        mData.mSymbolDatabase().functionScopes.push_back(scope);
        createTokensFunctionBody(tokenList, scope);
    } else {
        if (isDefault || isDelete || isPure) {
            addtoken(tokenList, "=");
            addtoken(tokenList, isDefault ? "default" : isDelete ? "delete" : "0");
        }
        addtoken(tokenList, ";");
    }
}

Function *clangimport::AstNode::getFunction(const TokenList &tokenList, Token *nameToken, const Token *retDef, const std::string &prev)
{
    auto *nestedIn = getTokenScope(nameToken);
    const std::string id = getId();
    if (!prev.empty()) {
        mData.ref(prev, nameToken);
        // later references might use the id of this declaration
        if (nameToken->function())
            mData.funcDecl(id, nameToken, const_cast<Function *>(nameToken->function()));
    }
    if (!nameToken->function()) {
        nestedIn->functionList.emplace_back(nameToken, getQualType());
        mData.funcDecl(id, nameToken, &nestedIn->functionList.back());
        if (mKind == CXXConstructorDecl) {
            nestedIn->functionList.back().type = FunctionType::eConstructor;
            nestedIn->numConstructors++;
        }
        else if (mKind == CXXDestructorDecl)
            nestedIn->functionList.back().type = FunctionType::eDestructor;
        else
            nestedIn->functionList.back().retDef = retDef;
    }

    auto * const function = const_cast<Function*>(nameToken->function());

    if (prev.empty()) {
        auto accessControl = mData.scopeAccessControl.find(tokenList.back()->scope());
        if (accessControl != mData.scopeAccessControl.end())
            function->access = accessControl->second;
    }
    return function;
}

Scope *clangimport::AstNode::createFunctionScope(Function *function, const Token *nameToken, const Scope *functionOf)
{
    SymbolDatabase &symbolDatabase = mData.mSymbolDatabase;
    auto *nestedIn = getTokenScope(nameToken);
    symbolDatabase.scopeList.emplace_back(symbolDatabase, nullptr, nestedIn);
    Scope *scope = &symbolDatabase.scopeList.back();
    scope->function = function;
    scope->classDef = nameToken; // TODO: pass into ctor
    scope->type = ScopeType::eFunction;
    scope->className = nameToken->str();
    scope->functionOf = functionOf;
    nestedIn->nestedList.push_back(scope);
    function->hasBody(true);
    function->functionScope = scope;
    return scope;
}

Token *clangimport::AstNode::createTokensFunctionArguments(TokenList &tokenList, Function *function, Scope *scope, const Scope *typeScope, bool declareArgs, bool newFunction)
{
    Token *par1 = addtoken(tokenList, "(");
    auto argIt = function->argumentList.begin();
    for (size_t i = 0; i < children.size(); ++i) {
        AstNodePtr child = children[i];
        if (child->mKind != ParmVarDecl)
            continue;
        if (tokenList.back() != par1)
            addtoken(tokenList, ",");
        std::stack<Token *> links;
        const Type *recordType = child->addTypeTokensBeforeName(tokenList, child->getQualType(), links, typeScope);
        const Token *typeEndToken = tokenList.back();
        const std::string spelling = child->getSpelling();
        Token *vartok = nullptr;
        if (!spelling.empty()) {
            vartok = child->addtoken(tokenList, spelling);
            // out of line member function: types are looked up in the class
            if (typeScope != vartok->scope() && !vartok->valueType())
                child->setValueType(vartok, child->getQualType(), typeScope);
        }
        child->addTypeTokensAfterName(tokenList, child->getQualType(), links);
        if (declareArgs) {
            Variable *var;
            Variable newVar(vartok, child->getQualType(), nullptr, typeEndToken, i, AccessControl::Argument, recordType, scope);
            if (newFunction || argIt == function->argumentList.end()) {
                function->argumentList.push_back(std::move(newVar));
                var = &function->argumentList.back();
            } else {
                // update the existing variable, tokens in the declaration point at it
                *argIt = newVar;
                var = &*argIt;
                ++argIt;
            }
            if (vartok)
                mData.varDecl(child->getId(), vartok, var);
        } else if (vartok) {
            mData.ref(child->getId(), vartok);
        }
    }
    Token *par2 = addtoken(tokenList, ")");
    Token::createMutualLinks(par1, par2);
    return par1;
}

Token *clangimport::AstNode::createTokensFunctionBody(TokenList &tokenList, Scope *scope)
{
    const AstNodePtr &body = children.back();
    Token *bodyStart = body->addtokenAtRange(tokenList, "{", "begin");
    bodyStart->scope(scope);
    body->createTokens(tokenList);
    Token *bodyEnd = body->addtokenAtRange(tokenList, "}", "end");
    scope->bodyStart = bodyStart;
    scope->bodyEnd = bodyEnd;
    Token::createMutualLinks(bodyStart, bodyEnd);
    return bodyStart;
}

// "[ & n ] ( int k ) { .. }". The closure class has the parameters and the body in operator().
Token *clangimport::AstNode::createTokensLambdaExpr(TokenList &tokenList)
{
    const AstNodePtr &closure = getChild(0);
    AstNodePtr method;
    std::vector<AstNodePtr> fields;
    for (const AstNodePtr &child: closure->children) {
        if (child && child->mKind == CXXMethodDecl && child->getSpelling() == "operator()")
            method = child;
        else if (child && child->mKind == FieldDecl)
            fields.push_back(child);
    }
    if (!method)
        return addtoken(tokenList, "?" + mKind + "?");

    // captures, the capture default "=" / "&" is not written in the JSON
    Token *bracket1 = addtoken(tokenList, "[", false);
    Token *captures = nullptr;
    for (std::size_t i = 1; i + 1 < children.size(); ++i) {
        Token *comma = captures ? addtoken(tokenList, ",", false) : nullptr;
        const bool byReference = i - 1 < fields.size() && endsWith(fields[i - 1]->getQualType(), '&');
        Token *amp = byReference ? addtoken(tokenList, "&", false) : nullptr;
        Token *capture = children[i]->createTokens(tokenList);
        if (amp) {
            amp->astOperand1(capture);
            capture = amp;
        }
        captures = comma ? setAstOperands(comma, captures, capture) : capture;
    }
    Token *bracket2 = addtoken(tokenList, "]", false);
    Token::createMutualLinks(bracket1, bracket2);

    // the lambda function and its scope
    Scope *nestedIn = getNestedInScope(tokenList);
    // the operator() of the closure is const, the lambda function is not const in the normal import
    std::string functionType = method->getQualType();
    if (endsWith(functionType, " const"))
        functionType.erase(functionType.size() - 6);
    nestedIn->functionList.emplace_back(bracket1, functionType);
    Function *function = &nestedIn->functionList.back();
    function->type = FunctionType::eLambda;
    function->clangSetFlags(true, false, false);
    function->token = bracket1;
    function->nestedIn = nestedIn;
    bracket1->function(function);
    SymbolDatabase &symbolDatabase = mData.mSymbolDatabase;
    symbolDatabase.scopeList.emplace_back(symbolDatabase, nullptr, nestedIn);
    Scope *scope = &symbolDatabase.scopeList.back();
    scope->type = ScopeType::eLambda;
    scope->classDef = bracket1;
    scope->className = bracket1->str();
    scope->function = function;
    nestedIn->nestedList.push_back(scope);
    function->hasBody(true);
    function->functionScope = scope;

    Token *par1 = method->createTokensFunctionArguments(tokenList, function, scope, nestedIn, true, true);
    function->argDef = par1;
    function->arg = par1;
    Token *bodyStart = method->createTokensFunctionBody(tokenList, scope);

    // AST: "[" => "(" => "{", the captures are the second operand of "["
    par1->astOperand1(bodyStart);
    return setAstOperands(bracket1, par1, captures);
}

void clangimport::AstNode::createTokensForCXXRecord(TokenList &tokenList)
{
    const std::string tagUsed = jsonString("tagUsed", "struct");
    Token * const classToken = addtoken(tokenList, tagUsed);
    const std::string className = getTypeName(tokenList) + getTemplateParameters();
    addtoken(tokenList, className);
    // base classes
    std::vector<::Type::BaseInfo> bases;
    if (isDefinition() && mJsonObject.count("bases")) {
        for (const picojson::value &baseValue: mJsonObject.at("bases").get<picojson::array>()) {
            const picojson::object &base = baseValue.get<picojson::object>();
            addtoken(tokenList, bases.empty() ? ":" : ",");
            ::Type::BaseInfo baseInfo;
            baseInfo.access = getAccessControl(getJsonString(base, "access"));
            const std::string writtenAccess = getJsonString(base, "writtenAccess", "none");
            if (writtenAccess != "none")
                addtoken(tokenList, writtenAccess);
            baseInfo.isVirtual = getJsonBool(base, "isVirtual");
            if (baseInfo.isVirtual)
                addtoken(tokenList, "virtual");
            // "N::B" => "N :: B"
            std::string name = getJsonQualType(base, "type");
            if (name.find('<') == std::string::npos) {
                std::string::size_type pos;
                while ((pos = name.find("::")) != std::string::npos) {
                    addtoken(tokenList, name.substr(0, pos));
                    addtoken(tokenList, "::");
                    name.erase(0, pos + 2);
                }
            }
            baseInfo.nameTok = addtoken(tokenList, name, false);
            baseInfo.name = name;
            baseInfo.type = mData.mSymbolDatabase().findVariableType(baseInfo.nameTok->scope(), baseInfo.nameTok);
            bases.push_back(std::move(baseInfo));
        }
    }

    // definition
    if (isDefinition()) {
        std::vector<AstNodePtr> children2;
        std::copy_if(children.cbegin(), children.cend(), std::back_inserter(children2), [](const AstNodePtr& child) {
            // skip implicit constructors etc that clang adds
            if (child->isImplicit())
                return false;
            return child->mKind == CXXConstructorDecl ||
                   child->mKind == CXXDestructorDecl ||
                   child->mKind == CXXMethodDecl ||
                   child->mKind == FieldDecl ||
                   child->mKind == VarDecl ||
                   child->mKind == AccessSpecDecl ||
                   child->mKind == CXXRecordDecl ||
                   child->mKind == EnumDecl;
        });
        Scope *scope = createScope(tokenList, getRecordScopeType(tagUsed), children2, classToken);
        mData.scopeDecl(getId(), scope);
        const_cast<::Type *>(scope->definedType)->derivedFrom = std::move(bases);
    }
    addtokenAtRange(tokenList, ";", "end");
    tokenList.back()->scope(classToken->scope());
}

const ::Type *clangimport::AstNode::addTypeTokensBeforeName(TokenList &tokenList, const std::string &qualType, std::stack<Token *> &links, const Scope *scope)
{
    std::string typeBefore = getQualTypeBefore(qualType);
    // function pointer: "int (*" => "int" + "( *"
    std::string declaratorBefore;
    const std::string::size_type par = typeBefore.find_last_of('(');
    if (par != std::string::npos && par + 1 < typeBefore.size() && (typeBefore[par + 1] == '*' || typeBefore[par + 1] == '&')) {
        declaratorBefore = typeBefore.substr(par);
        typeBefore.erase(par);
    }
    const ::Type *recordType = addTypeTokens(tokenList, typeBefore, scope);
    addDeclaratorTokens(tokenList, declaratorBefore, links);
    return recordType;
}

void clangimport::AstNode::addTypeTokensAfterName(TokenList &tokenList, const std::string &qualType, std::stack<Token *> &links)
{
    const std::string qualTypeAfter = getQualTypeAfter(qualType);
    if (!links.empty())
        addDeclaratorTokens(tokenList, qualTypeAfter, links);
    else if (!qualTypeAfter.empty())
        addTypeTokens(tokenList, qualTypeAfter);
}

/** tokens in a declarator "(*" ... ")(int)", parentheses are linked across the name */
void clangimport::AstNode::addDeclaratorTokens(TokenList &tokenList, const std::string &str, std::stack<Token *> &links)
{
    std::string::size_type pos = 0;
    while (pos < str.size()) {
        if (str[pos] == ' ') {
            ++pos;
            continue;
        }
        std::string::size_type end = pos + 1;
        if (std::isalnum(static_cast<unsigned char>(str[pos])) || str[pos] == '_') {
            while (end < str.size() && (std::isalnum(static_cast<unsigned char>(str[end])) || str[end] == '_'))
                ++end;
        } else if (str.compare(pos, 2, "&&") == 0 || str.compare(pos, 2, "::") == 0) {
            end = pos + 2;
        }
        Token *tok = addtoken(tokenList, str.substr(pos, end - pos), false);
        if (Token::Match(tok, "(|["))
            links.push(tok);
        else if (Token::Match(tok, ")|]") && !links.empty()) {
            Token::createMutualLinks(links.top(), tok);
            links.pop();
        }
        pos = end;
    }
}

Token * clangimport::AstNode::createTokensVarDecl(TokenList &tokenList, const Variable *baseVar, const Token *baseTypeEnd, const std::string &baseType)
{
    const std::string id = getId();
    const std::string qualType = getQualType();
    const std::string name = getSpelling();
    const Token *startToken;
    const Token *typeEndToken;
    const ::Type *recordType;
    std::stack<Token *> links;
    if (baseVar) {
        // the base type tokens are shared, only add the rest of the type: "int i, *p" => "* p"
        startToken = baseVar->typeStartToken();
        recordType = baseVar->type();
        const std::string typeBefore = getQualTypeBefore(qualType);
        if (typeBefore.size() > baseType.size()) {
            const std::string rest = typeBefore.substr(baseType.size());
            if (rest.find("(*") != std::string::npos || rest.find("(&") != std::string::npos)
                addDeclaratorTokens(tokenList, rest, links);
            else
                addTypeTokens(tokenList, rest);
            typeEndToken = tokenList.back();
        } else {
            typeEndToken = baseTypeEnd;
        }
    } else {
        const std::string storageClass = getStorageClass();
        if (storageClass == "static" || storageClass == "extern")
            addtoken(tokenList, storageClass);
        startToken = tokenList.back();
        recordType = addTypeTokensBeforeName(tokenList, qualType, links);
        if (!startToken)
            startToken = tokenList.front();
        else if (!Token::Match(startToken, "static|extern"))
            startToken = startToken->next();
        typeEndToken = tokenList.back();
    }
    Token *vartok1 = name.empty() ? nullptr : addtoken(tokenList, name);
    addTypeTokensAfterName(tokenList, qualType, links);
    Scope *scope = getTokenScope(tokenList.back());
    // exception declaration "catch (int e)"
    const AccessControl access = Token::simpleMatch(startToken->tokAt(-2), "catch (") ? AccessControl::Throw : scope->defaultAccess();
    scope->varlist.emplace_back(vartok1, qualType, startToken, typeEndToken, scope->varlist.size(), access, recordType, scope);
    Variable *var = &scope->varlist.back();
    mData.varDecl(id, vartok1, var);
    Token *ret = createTokensVarInit(tokenList, vartok1, recordType);
    var->clangSetInitialization();
    return ret;
}

Token * clangimport::AstNode::createTokensVarInit(TokenList &tokenList, Token *vartok1, const ::Type *recordType)
{
    std::string init = jsonString("init");
    // default member initializer
    // clang does not say if "=" was written, assume "x{..}" unless it is an array
    if (mKind == FieldDecl && jsonBool("hasInClassInitializer"))
        init = (!children.empty() && children.back()->mKind == InitListExpr && !vartok1->variable()->isArray()) ? "list" : "c";
    if (!children.empty() && init == "c") {
        Token *eq = addtoken(tokenList, "=");
        return setAstOperands(eq, vartok1, children.back()->createTokens(tokenList));
    }
    if (!children.empty() && (init == "call" || init == "list")) {
        AstNodePtr expr = children.back();
        if (expr->mKind == ExprWithCleanups && !expr->children.empty())
            expr = expr->children[0];
        // "S s;" => clang adds a call to the default constructor
        if (init == "call" && expr->mKind == CXXConstructExpr && expr->children.empty())
            return vartok1;
        Token *par1 = expr->createTokensInitArgs(tokenList, vartok1);
        // constructor call
        if (recordType)
            setValueType(par1);
        return par1;
    }
    return vartok1;
}

/** set the record type of the type tokens in "sizeof ( S )" */
static void setTypes(TokenList &tokenList)
{
    for (Token *tok = tokenList.front(); tok; tok = tok->next()) {
        if (Token::simpleMatch(tok, "sizeof (")) {
            for (Token *typeToken = tok->tokAt(2); typeToken->str() != ")"; typeToken = typeToken->next()) {
                if (typeToken->type())
                    continue;
                typeToken->type(typeToken->scope()->findType(typeToken->str()));
            }
        }
    }
}

/** size of record types and values of sizeof */
static void setValues(const Tokenizer &tokenizer, const SymbolDatabase *symbolDatabase)
{
    const Settings & settings = tokenizer.getSettings();

    for (const Scope& scope : symbolDatabase->scopeList) {
        if (!scope.definedType)
            continue;

        MathLib::bigint typeSize = 0;
        for (const Variable &var: scope.varlist) {
            const MathLib::bigint mul = std::accumulate(var.dimensions().cbegin(), var.dimensions().cend(), MathLib::bigint(1), [](MathLib::bigint v, const Dimension& dim) {
                return v * dim.num;
            });
            if (var.valueType())
                typeSize += mul * var.valueType()->getSizeOf(settings, ValueType::Accuracy::ExactOrZero, ValueType::SizeOf::Pointer);
        }
        scope.definedType->sizeOf = typeSize;
    }

    for (auto *tok = const_cast<Token*>(tokenizer.tokens()); tok; tok = tok->next()) {
        if (Token::simpleMatch(tok, "sizeof (")) {
            ValueType vt = ValueType::parseDecl(tok->tokAt(2), settings);
            const size_t sz = vt.getSizeOf(settings, ValueType::Accuracy::ExactOrZero, ValueType::SizeOf::Pointer);
            if (sz == 0)
                continue;
            long long mul = 1;
            for (const Token *arrtok = tok->linkAt(1)->previous(); arrtok; arrtok = arrtok->previous()) {
                const std::string &a = arrtok->str();
                if (a.size() > 2 && a[0] == '[' && a.back() == ']')
                    mul *= strToInt<long long>(a.substr(1));
                else
                    break;
            }
            ValueFlow::Value v(mul * sz);
            v.setKnown();
            tok->next()->addValue(v);
        }
    }
}

/** Child nodes. For "int a[3] = {1};" clang writes the elements in "array_filler" after the filler. */
static std::vector<const picojson::value *> getInner(const picojson::object& obj)
{
    std::vector<const picojson::value *> ret;
    if (obj.count("array_filler") && obj.at("array_filler").is<picojson::array>()) {
        const picojson::array &arrayFiller = obj.at("array_filler").get<picojson::array>();
        for (std::size_t i = 1; i < arrayFiller.size(); ++i)
            ret.push_back(&arrayFiller[i]);
    }
    if (obj.count("inner") && obj.at("inner").is<picojson::array>()) {
        for (const picojson::value& child: obj.at("inner").get<picojson::array>())
            ret.push_back(&child);
    }
    return ret;
}

/** create the AstNode tree for the JSON */
static void parseTree(clangimport::AstNode& astNode, clangimport::Data &data) {
    for (const picojson::value *child: getInner(astNode.getJsonObject())) {
        const picojson::object& childObject = child->get<picojson::object>();
        if (childObject.count("kind") == 0) {
            astNode.children.push_back({});
            continue;
        }

        astNode.children.emplace_back(std::make_shared<clangimport::AstNode>(childObject, data));
        parseTree(*astNode.children.back(), data);
    }
}

namespace {
    /** The previous location written by clang */
    struct LastLocation {
        std::string file;
        int64_t line = 0;
    };
}

/**
 * Clang only writes "file" and "line" in a location when they differ from
 * the previously written location. Add them to each location.
 */
static void completeLocation(picojson::value &value, LastLocation &last)
{
    if (!value.is<picojson::object>())
        return;
    picojson::object &loc = value.get<picojson::object>();
    if (loc.count("spellingLoc") || loc.count("expansionLoc")) {
        // macro: clang writes the spelling location first
        if (loc.count("spellingLoc"))
            completeLocation(loc["spellingLoc"], last);
        if (loc.count("expansionLoc"))
            completeLocation(loc["expansionLoc"], last);
        return;
    }
    if (!loc.count("col"))
        return; // invalid location
    if (loc.count("file") && loc.at("file").is<std::string>())
        last.file = loc.at("file").get<std::string>();
    else
        loc["file"] = picojson::value(last.file);
    if (loc.count("line") && loc.at("line").is<int64_t>())
        last.line = loc.at("line").get<int64_t>();
    else
        loc["line"] = picojson::value(last.line);
}

static void completeLocations(picojson::value &value, LastLocation &last)
{
    if (!value.is<picojson::object>())
        return;
    picojson::object &node = value.get<picojson::object>();
    if (node.count("loc"))
        completeLocation(node["loc"], last);
    if (node.count("range") && node["range"].is<picojson::object>()) {
        picojson::object &range = node["range"].get<picojson::object>();
        if (range.count("begin"))
            completeLocation(range["begin"], last);
        if (range.count("end"))
            completeLocation(range["end"], last);
    }
    for (const char *key: {"array_filler", "inner"}) {
        if (node.count(key) && node[key].is<picojson::array>()) {
            for (picojson::value &child: node[key].get<picojson::array>())
                completeLocations(child, last);
        }
    }
}

/** Collect names of "typedef struct { .. } T;" */
static void collectTypedefNames(const picojson::value &value, std::map<std::string, std::string> &typedefNames)
{
    if (!value.is<picojson::object>())
        return;
    const picojson::object &node = value.get<picojson::object>();
    if (!node.count("inner") || !node.at("inner").is<picojson::array>())
        return;
    const picojson::array &inner = node.at("inner").get<picojson::array>();
    if (getJsonString(node, "kind") == TypedefDecl && node.count("name") && !inner.empty() && inner[0].is<picojson::object>()) {
        const picojson::object *tagDecl = findJsonObject(inner[0].get<picojson::object>(), "ownedTagDecl");
        if (tagDecl && tagDecl->count("id") && getJsonString(*tagDecl, "name").empty())
            typedefNames.emplace(getJsonString(*tagDecl, "id"), getJsonString(node, "name"));
    }
    for (const picojson::value &child: inner)
        collectTypedefNames(child, typedefNames);
}

/** Collect label names. A GotoStmt only has the id of the label. */
static void collectLabelNames(const picojson::value &value, std::map<std::string, std::string> &labelNames)
{
    if (!value.is<picojson::object>())
        return;
    const picojson::object &node = value.get<picojson::object>();
    if (getJsonString(node, "kind") == LabelStmt && node.count("declId") && node.count("name"))
        labelNames[getJsonString(node, "declId")] = getJsonString(node, "name");
    if (node.count("inner") && node.at("inner").is<picojson::array>()) {
        for (const picojson::value &child: node.at("inner").get<picojson::array>())
            collectLabelNames(child, labelNames);
    }
}

/** create tokens for all top level declarations */
static void parseTranslationUnitDecl(TokenList& tokenList, clangimport::Data &data, const picojson::object& obj) {
    if (obj.count("kind") == 0)
        return;
    const std::string kind = obj.at("kind").get<std::string>();
    if (kind == TranslationUnitDecl && obj.count("inner")) {
        for (const picojson::value& child: obj.at("inner").get<picojson::array>()) {
            clangimport::AstNode astNode(child.get<picojson::object>(), data);
            parseTree(astNode, data);
            astNode.createTokens1(tokenList);
        }
    }
}

void clangimport::parseClangAstDump(Tokenizer &tokenizer, const std::string &json)
{
    TokenList &tokenList = tokenizer.list;

    tokenizer.createSymbolDatabase();
    auto *symbolDatabase = const_cast<SymbolDatabase *>(tokenizer.getSymbolDatabase());
    symbolDatabase->scopeList.emplace_back(*symbolDatabase, nullptr, nullptr);
    symbolDatabase->scopeList.back().type = ScopeType::eGlobal;

    picojson::value res;
    const std::string err = picojson::parse(res, json);
    if (!err.empty())
        throw InternalError(nullptr, "Failed to parse Clang AST. Bad JSON format: " + err);
    if (!res.is<picojson::object>())
        throw InternalError(nullptr, "Failed to parse Clang AST. Bad JSON format: Not an object");

    clangimport::Data data(tokenizer.getSettings(), *symbolDatabase);

    // pre-passes
    LastLocation lastLocation;
    completeLocations(res, lastLocation);
    collectLabelNames(res, data.mLabelNames);
    collectTypedefNames(res, data.mTypedefNames);

    parseTranslationUnitDecl(tokenList, data, res.get<picojson::object>());

    // Validation
    for (const Token *tok = tokenList.front(); tok; tok = tok->next()) {
        if (Token::Match(tok, "(|)|[|]|{|}") && !tok->link())
            throw InternalError(tok, "Token::link() is not set properly");
    }

    // remaining symbol database information
    if (tokenList.front())
        tokenList.front()->assignIndexes();
    symbolDatabase->clangSetVariables(data.getVariableList());
    symbolDatabase->clangCreateSymbolDatabaseInfo();
    symbolDatabase->createSymbolDatabaseExprIds();
    tokenList.clangSetOrigFiles();
    setTypes(tokenList);
    setValues(tokenizer, symbolDatabase);
}

