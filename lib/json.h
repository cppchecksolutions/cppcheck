/*
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2023 Cppcheck team.
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

#ifndef jsonH
#define jsonH

#include "config.h"
#include <stdexcept>
#include <string>

SUPPRESS_WARNING_PUSH("-Wfloat-equal")
SUPPRESS_WARNING_CLANG_PUSH("-Wtautological-type-limit-compare")
SUPPRESS_WARNING_CLANG_PUSH("-Wextra-semi-stmt")
SUPPRESS_WARNING_CLANG_PUSH("-Wzero-as-null-pointer-constant")

#define PICOJSON_USE_INT64
#include <picojson.h>

SUPPRESS_WARNING_CLANG_POP
SUPPRESS_WARNING_CLANG_POP
SUPPRESS_WARNING_CLANG_POP
SUPPRESS_WARNING_POP

namespace cppcheck {
    class JsonError : public std::runtime_error {
    public:
        explicit JsonError(const std::string& msg) : std::runtime_error(msg) {}
    };

    template<class T>
    std::string typeName() {
        if (std::is_same<T, std::string>::value)
            return "string";
        else if (std::is_same<T, bool>::value)
            return "boolean";
        else if (std::is_same<T, int64_t>::value)
            return "integer";
        else if (std::is_same<T, picojson::object>::value)
            return "object";
        else if (std::is_same<T, picojson::array>::value)
            return "array";
        return "unknown";
    }

    template<class T>
    T read(const picojson::object &obj, const std::string& name) {
        const auto it = obj.find(name);
        if (it == obj.cend())
            throw JsonError("'" + name + "' does not exist.");
        const auto& val = it->second;
        if (!val.is<T>())
            throw JsonError("'" + name + "' is not a " + typeName<T>() + ".");
        return val.get<T>();
    }

    template<class T>
    T readOptional(const picojson::object &obj, const std::string& name, T defaultValue = T()) {
        const auto it = obj.find(name);
        if (it == obj.cend())
            return defaultValue;
        const auto& val = it->second;
        if (!val.is<T>())
            throw JsonError("'" + name + "' is not a " + typeName<T>() + ".");
        return val.get<T>();
    }

    template<class T>
    std::vector<T> readOptionalArray(const picojson::object &obj, const std::string& name) {
        const auto it = obj.find(name);
        if (it == obj.cend())
            return {};
        const auto& arr = it->second;
        if (!arr.is<picojson::array>())
            throw JsonError("'" + name + "' is not an array.");
        std::vector<T> result;
        for (const picojson::value &val: arr.get<picojson::array>()) {
            if (!val.is<T>())
                throw JsonError("'" + name + "' entry is not a " + typeName<T>() + ".");
            result.push_back(val.get<T>());
        }
        return result;
    }


    bool readOptionalBool(const picojson::object &obj, const std::string& name, bool defaultValue=false);
    std::string readOptionalString(const picojson::object &obj, const std::string& name, const std::string defaultValue = "");
    int64_t readInt(const picojson::object &obj, const std::string& name);
    std::string readString(const picojson::object &obj, const std::string& name);
    std::vector<std::string> readOptionalStringArray(const picojson::object &obj, const std::string& name);
}

#endif // jsonH
