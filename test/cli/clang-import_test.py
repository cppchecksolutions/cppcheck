
# python -m pytest test-clang-import.py

import os
import re
import subprocess
import sys
import pytest
from testutils import cppcheck, assert_cppcheck

try:
    # TODO: handle exitcode?
    subprocess.call(['clang', '--version'])
except OSError:
    pytest.skip("'clang' does not exist", allow_module_level=True)


# the IDs differ with Visual Studio
if sys.platform == 'win32':
    pytest.skip(allow_module_level=True)


def __get_debug_section(title, stdout):
    s = re.sub(r'0x[0-9a-fA-F]+', '0x12345678', stdout)
    s = re.sub(r'nestedIn: Struct', 'nestedIn: Class', s)
    s = re.sub(r'classDef: struct', 'classDef: class', s)
    s = re.sub(r'isInline: [a-z]+', 'isInline: ---', s)
    s = re.sub(r'needInitialization: .*', 'needInitialization: ---', s)
    s = re.sub(r'functionOf: .*', 'functionOf: ---', s)
    s = re.sub(r'0x12345678 Struct', '0x12345678 Class', s)

    if title == '##AST':
        # TODO set types
        s = re.sub(r"return '[a-zA-Z0-9: *]+'", "return", s)

    pos1 = s.find(title)
    assert pos1 > 0, 'title not found'
    pos1 = s.find('\n', pos1) + 1
    assert pos1 > 0
    pos2 = s.find("\n##", pos1)
    if pos2 < 0:
        return s[pos1:]
    return s[pos1:pos2-1]


def __check_symbol_database(tmpdir, code):
    testfile = os.path.join(tmpdir, 'test.cpp')
    with open(testfile, 'w+t') as f:
        f.write(code)
    ret1, stdout1, _ = cppcheck(['-q', '--clang', '--debug-symdb', testfile])
    ret2, stdout2, _ = cppcheck(['-q', '--debug-symdb', testfile])
    assert 0 == ret1, stdout1
    assert 0 == ret2, stdout2
    assert __get_debug_section('### Symbol database', stdout1) == __get_debug_section('### Symbol database', stdout2)


def __check_ast(tmpdir, code):
    testfile = os.path.join(tmpdir, 'test.cpp')
    with open(testfile, 'w+t') as f:
        f.write(code)
    ret1, stdout1, _ = cppcheck(['-q', '--clang', '--debug-ast', testfile])
    ret2, stdout2, _ = cppcheck(['-q', '--debug-ast', testfile])
    assert 0 == ret1, stdout1
    assert 0 == ret2, stdout1
    assert __get_debug_section('##AST', stdout1) == __get_debug_section('##AST', stdout2)



def test_symbol_database_1(tmpdir):
    __check_symbol_database(tmpdir, 'int main(){return 0;}')

def test_symbol_database_2(tmpdir):
    __check_symbol_database(tmpdir, 'struct Foo { void f(); }; void Foo::f() {}')

def test_symbol_database_3(tmpdir):
    __check_symbol_database(tmpdir, 'struct Fred { int a; }; int b; void f(int c, int d) { int e; }')

def test_symbol_database_4(tmpdir):
    __check_symbol_database(tmpdir, 'void f(const int x) {}')

def test_symbol_database_5(tmpdir):
    __check_symbol_database(tmpdir, 'void f(int);')

def test_symbol_database_6(tmpdir):
    __check_symbol_database(tmpdir, 'inline static int foo(int x) { return x; }')

def test_symbol_database_7(tmpdir):
    __check_symbol_database(tmpdir, 'struct S {int x;}; void f(struct S *s) {}')

def test_symbol_database_class_access_1(tmpdir):
    __check_symbol_database(tmpdir, 'class Fred { void foo ( ) {} } ;')

def test_symbol_database_class_access_2(tmpdir):
    __check_symbol_database(tmpdir, 'class Fred { protected: void foo ( ) {} } ;')

def test_symbol_database_class_access_3(tmpdir):
    __check_symbol_database(tmpdir, 'class Fred { public: void foo ( ) {} } ;')

def test_symbol_database_operator(tmpdir):
    __check_symbol_database(tmpdir, 'struct Fred { void operator=(int x); };')

def test_symbol_database_enum(tmpdir):
    __check_symbol_database(tmpdir, 'enum E { A, B, C }; int f() { enum L { M }; return C + M; }')

def test_symbol_database_enum_values(tmpdir):
    __check_symbol_database(tmpdir, 'enum E { A, B = 5, C, F = 1 << 4, G = B + 1 };')

def test_symbol_database_enum_anonymous(tmpdir):
    __check_symbol_database(tmpdir, 'enum { A, B } x; enum { C }; int f() { return x == B; }')

def test_symbol_database_variable_index(tmpdir):
    __check_symbol_database(tmpdir, 'int x; int y; struct S { int a; int b; int c; }; void f() { int l1; int l2; }')

def test_symbol_database_block_scope(tmpdir):
    __check_symbol_database(tmpdir, 'void f(int x) { int a; { int b; { int c; } } switch (x) { case 1: { int d; break; } default: { int e; } } }')

def test_symbol_database_enum_variables(tmpdir):
    __check_symbol_database(tmpdir, 'enum E { A } x, *px; void f(enum E e, enum E *pe) { enum E le; }')

def test_symbol_database_declstmt(tmpdir):
    __check_symbol_database(tmpdir, 'void f() { int a, b = 2, *c; enum { L } l = L; }')

def test_symbol_database_namespace(tmpdir):
    __check_symbol_database(tmpdir, 'namespace N { int v; int g() { return v; } namespace M { int w; } }\n'
                                    'namespace N { int v2; }\n'
                                    'using namespace N;\n'
                                    'int f() { return v + v2; }')

def test_symbol_database_extern(tmpdir):
    __check_symbol_database(tmpdir, 'extern int e; extern const int *ep; extern int g(); void f() { extern int le; static int ls; le = ls; }')

def test_symbol_database_implicit_members(tmpdir):
    # clang adds implicit constructors
    __check_symbol_database(tmpdir, 'struct S { int m; }; void f(S *a, S *b) { *a = *b; }')

def test_symbol_database_struct_1(tmpdir):
    __check_symbol_database(tmpdir, 'struct S {};')

def test_ast_calculations(tmpdir):
    __check_ast(tmpdir, 'int x = 5; int y = (x + 4) * 2;')
    __check_ast(tmpdir, 'long long dostuff(int x) { return x ? 3 : 5; }')

@pytest.mark.parametrize('code', ('void foo(int x) { if (x > 5){} }',
                                  'void dostuff() { for (int x = 0; x < 10; x++); }',
                                  'void foo(int x) { switch (x) {case 1: break; } }',
                                  'void foo(int a, int b, int c) { foo(a,b,c); }'))
def test_ast_control_flow(tmpdir, code):
    __check_ast(tmpdir, code)

def test_ast_valuetype_sign(tmpdir):
    __check_ast(tmpdir, 'unsigned long a; unsigned char b; signed char c; unsigned d; long long e; unsigned short f;\n'
                        'void foo() { a = 1; b = 2; c = 3; d = 4; e = 5; f = 6; }')

def test_ast_qualified_names(tmpdir):
    __check_ast(tmpdir, 'namespace N { int v; namespace M { int w; } } struct S { static int s; };\n'
                        'int f() { return N::v + N::M::w + S::s; }')

def test_symbol_database_std_types(tmp_path):
    # "unsigned int" => one token "int" with unsigned flag, same as normal tokenizer
    for ext in ('c', 'cpp'):
        test_file = tmp_path / ('test.' + ext)
        with open(test_file, 'wt') as f:
            f.write('unsigned int a; long long b; const unsigned char *c;\n')
        ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
        assert ret == 0, stdout
        assert 'mTypeStartToken: unsigned' not in stdout
        assert stdout.count('mTypeStartToken: int ') == 1, stdout
        assert stdout.count('mTypeStartToken: long ') == 1, stdout
        assert stdout.count('mTypeStartToken: char ') == 1, stdout

def test_ast(tmpdir):
    __check_ast(tmpdir, 'struct S { int x; }; S* foo() { return new S(); }')

def test_log(tmpdir):
    test_file = os.path.join(tmpdir, 'test.cpp')
    with open(test_file, 'wt'):
        pass

    args = ['--clang', test_file]
    out_lines = [
        'Checking {} ...'.format(test_file).replace('\\', '/'),
    ]

    assert_cppcheck(args, ec_exp=0, err_exp=[], out_exp=out_lines)


def test_include(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('#include "test.h"')

    with open(tmp_path / 'test.h', 'wt') as f:
        f.write('int x;\n')

    exitcode, stdout, stderr = cppcheck(['-q', '--clang', '--debug', str(test_file)])
    assert exitcode == 0, stderr if not stdout else stdout
    # the number of empty lines after "##file" depends on the builtin declarations in the clang AST dump
    assert '##file {}\n'.format(tmp_path / 'test.h') in stdout, stdout
    assert '\n1: int x@var1 ;\n' in stdout, stdout


def test_warning(tmpdir):  # #12424
    test_file = os.path.join(tmpdir, 'test_2')
    with open(test_file, 'wt') as f:
        f.write('''void f() {}''')

    exitcode, stdout, stderr = cppcheck(['-q', '--enable=warning', '--clang', test_file])
    assert exitcode == 0, stderr # do not assert
    assert stdout == ''
    assert stderr == ''


def __test_cmd(tmp_path, file_name, extra_args, stdout_exp_1, content=''):
    test_file = tmp_path / file_name
    with open(test_file, 'wt') as f:
        f.write(content)

    args = [
        '--enable=information',
        '--verbose',
        '--clang',
        file_name
    ]

    args += extra_args

    if stdout_exp_1:
        stdout_exp_1 += ' '

    exitcode, stdout, stderr = cppcheck(args, cwd=tmp_path)
    assert exitcode == 0, stderr if not stdout else stdout
    assert stderr == ''
    assert stdout.splitlines() == [
        'Checking {} ...'.format(file_name),
        'clang -fsyntax-only -Xclang -ast-dump=json -fno-color-diagnostics {}{}'.format(stdout_exp_1, file_name)
    ]


def test_cmd_c(tmp_path):
    __test_cmd(tmp_path, 'test.c', [], '-x c')


def test_cmd_cpp(tmp_path):
    __test_cmd(tmp_path, 'test.cpp', [], '-x c++')


# files with unknown extensions are treated as C++
def test_cmd_unk(tmp_path):
    __test_cmd(tmp_path, 'test.cplusplus', [], '-x c++')


# headers are treated as C by default
def test_cmd_hdr(tmp_path):
    __test_cmd(tmp_path, 'test.h', [], '-x c')


def test_cmd_hdr_probe(tmp_path):
    __test_cmd(tmp_path, 'test.h', ['--cpp-header-probe'], '-x c++', '// -*- C++ -*-')


def test_cmd_inc(tmp_path):
    inc_path = tmp_path / 'inc'
    os.makedirs(inc_path)
    __test_cmd(tmp_path, 'test.cpp',['-Iinc'], '-x c++ -Iinc/')


def test_cmd_def(tmp_path):
    __test_cmd(tmp_path, 'test.cpp',['-DDEF'], '-x c++ -DDEF=1')


def test_cmd_include(tmp_path):
    inc_file = tmp_path / 'inc.h'
    with open(inc_file, 'wt'):
        pass
    __test_cmd(tmp_path, 'test.cpp',['--include=inc.h'], '-x c++ --include inc.h')


def test_cmd_enforce_c(tmp_path):  # #13128
    __test_cmd(tmp_path, 'test.cpp',['-x', 'c'], '-x c')


def test_cmd_enforce_cpp(tmp_path):  # #13128
    __test_cmd(tmp_path, 'test.c',['-x', 'c++'], '-x c++')


def test_cmd_std_c(tmp_path):  # #13129
    __test_cmd(tmp_path, 'test.cpp',['--std=c89', '--std=c++14'], '-x c++ -std=c++14')


# TODO: remove when we inject the build-dir into all tests
def test_cmd_std_c_builddir(tmp_path):  # #13129
    build_dir = tmp_path / 'b1'
    os.makedirs(build_dir)
    __test_cmd(tmp_path, 'test.cpp',['--std=c89', '--std=c++14', '--cppcheck-build-dir={}'.format(build_dir)], '-x c++ -std=c++14')


def test_cmd_std_cpp(tmp_path):  # #13129
    __test_cmd(tmp_path, 'test.c',['--std=c89', '--std=c++14'], '-x c -std=c89')


def test_cmd_std_c_enforce(tmp_path):  # #13128/#13129
    __test_cmd(tmp_path, 'test.cpp',['--language=c', '--std=c89', '--std=c++14'], '-x c -std=c89')


def test_cmd_std_cpp_enforce(tmp_path):  # #13128/#13129
    __test_cmd(tmp_path, 'test.c',['--language=c++', '--std=c89', '--std=c++14'], '-x c++ -std=c++14')


def test_cmd_std_c_enforce_alias(tmp_path):  # #13128/#13129/#13130
    __test_cmd(tmp_path, 'test.c',['--language=c', '--std=gnu99', '--std=gnu++11'], '-x c -std=gnu99')


def test_cmd_std_c_enforce_alias_2(tmp_path):  # #13128/#13129/#13130
    __test_cmd(tmp_path, 'test.c',['--language=c', '--std=iso9899:1999', '--std=gnu++11'], '-x c -std=iso9899:1999')


def test_cmd_std_cpp_enforce_alias(tmp_path):  # #13128/#13129/#13130
    __test_cmd(tmp_path, 'test.c',['--language=c++', '--std=gnu99', '--std=gnu++11'], '-x c++ -std=gnu++11')


@pytest.mark.xfail(strict=True)
def test_debug_clang_output(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write(
"""
void f() {}
""")

    args = [
        '-q',
        '--clang',
        '--debug-clang-output',
        str(test_file)
    ]

    exitcode, stdout, stderr = cppcheck(args)
    assert exitcode == 0, stderr if not stdout else stdout
    assert stderr == ''
    assert stdout.startswith('TranslationUnitDecl'), stdout
    assert stdout.find(str(test_file)) != -1, stdout


def test_debug_clang_output_failure_exitcode(tmp_path):
    # the given code will cause clang to fail with an exitcode
    #
    # Failed to execute 'clang -fsyntax-only -Xclang -ast-dump=json -fno-color-diagnostics -x c++ a.cpp 2>&1' - (exitcode: 1 / output: a.cpp:3:12: error: indirection requires pointer operand ('int' invalid)
    # 3 |     (void)(*0);
    # |            ^~
    # 1 error generated.
    # TranslationUnitDecl 0x6127d5d9d4e8 <<invalid sloc>> <invalid sloc>
    # ...
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write(
"""void f()
{
    (void)(*0);
}
""")

    args = [
        '-q',
        '--clang',
        '--debug-clang-output',
        '--no-cppcheck-build-dir',  # TODO: test without this?
        str(test_file)
    ]

    exitcode, stdout, stderr = cppcheck(args)
    assert exitcode == 0, stderr if not stdout else stdout
    stderr_lines = stderr.splitlines()
    assert len(stderr_lines) > 5, stderr_lines
    assert (stderr_lines[0] ==
            "Failed to execute 'clang -fsyntax-only -Xclang -ast-dump=json -fno-color-diagnostics -x c {} 2>&1' - (exitcode: 1 / output: {}:3:12: error: indirection requires pointer operand ('int' invalid)".format(test_file, test_file))
    assert stdout.find('TranslationUnitDecl') != -1, stdout
    assert stdout.find(str(test_file)) != -1, stdout


def _run_cppcheck_debug(test_file, code):
    with open(test_file, 'wt') as f:
        f.write(code+'\n')

    args = [
        '-q',
        '--clang',
        '--debug',
        str(test_file)
    ]

    _, stdout, stderr = cppcheck(args)
    assert stderr == ''
    return stdout


def test_tokens_vardecl1(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nint x = 5;')
    assert '2: int x@var1 = 5 ;' in stdout


def test_tokens_vardecl2(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nint x[10];')
    assert '2: int x@var1 [ 10 ] ;' in stdout


def test_tokens_vardecl3(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nstatic int x;')
    assert '2: static int x@var1 ;' in stdout


def test_tokens_stringliteral(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nconst char *s = "a\\"b";')
    assert '2: const char * s@var1 = "a\\"b" ;' in stdout


def test_tokens_floatingliteral(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\ndouble d = 1.5;\nfloat f = 2.0f;\ndouble e = 1e10;')
    assert '2: double d@var1 = 1.5 ;' in stdout
    assert '3: float f@var2 = 2.0 ;' in stdout
    assert '4: double e@var3 = 1.0E+10 ;' in stdout


def test_tokens_sizeof(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nint x[4];\nint a = sizeof(int);\nint b = sizeof x;\nint c = sizeof(x[0]);')
    assert '3: int a@var2 = sizeof ( int ) ;' in stdout
    assert '4: int b@var3 = sizeof ( x@var1 ) ;' in stdout
    assert '5: int c@var4 = sizeof ( x@var1 [ 0 ] ) ;' in stdout


def test_tokens_enum(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nenum E { A, B };\nint f(void) { enum L { M }; return B + M; }')
    assert '2: enum E { A , B } ;' in stdout
    assert '3: int f ( ) { enum L { M } ; return B@exprUNIQUE +@exprUNIQUE M@exprUNIQUE ; }' in stdout


def test_symbol_database_enum_values_c(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('enum E { A, B = 5, C, F = 1 << 4, G = B + 1 };\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    assert 'Enumerator: B = 5 [5]' in stdout
    assert 'Enumerator: C = 6\n' in stdout
    assert 'Enumerator: F = 16 [1 << 4]' in stdout
    assert 'Enumerator: G = 6 [B + 1]' in stdout


def test_tokens_enum_anonymous(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nenum { A, B } x;\nenum { C } y;')
    assert '2: enum Anonymous0 { A , B } ; enum Anonymous0 x@var1 ;' in stdout
    assert '3: enum Anonymous1 { C } ; enum Anonymous1 y@var2 ;' in stdout


def test_symbol_database_enum_variables_c(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('enum E { A } x, *px;\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    assert stdout.count('mTypeStartToken: E ') == 2, stdout
    assert 'mTypeStartToken: enum' not in stdout


def test_ast_enum_values(tmp_path):
    # getEnumType() reads the AST of the enumerator values
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('enum E { A, B = 5 };\nint f(enum E e) { return e == B; }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    assert "=\n|-B 'signed int'\n`-5 'signed int'" in stdout


def test_tokens_enum_class(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nenum class E : unsigned char { A, B };')
    assert '2: enum class E : unsigned char { A , B } ;' in stdout


def test_tokens_declstmt(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(void) {\nint a, b, *c;\nstruct S { int m; } s;\n}')
    assert '3: int a@var1 ; int b@var2 ; int * c@var3 ;' in stdout
    assert '4: struct S { int m@var4 ; } ; struct S s@var5 ;' in stdout


def test_tokens_extern(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nextern int e;\nextern int g(void);')
    assert '2: extern int e@var1 ;' in stdout
    assert '3: extern int g ( ) ;' in stdout


def test_tokens_typedefdecl(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\ntypedef unsigned int T;\nT x;')
    assert '3: unsigned int x@var1 ;' in stdout


def test_tokens_declrefexpr(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nconst int x = 5;\nconst int y = x;')
    assert '2: const int x@var1 = 5 ;' in stdout
    assert '3: const int y@var2 = x@var1 ;' in stdout


def test_tokens_function1(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid foo(){}')
    assert '2: void foo ( ) { }' in stdout


def test_tokens_function2(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nstatic int foo()\n{\n return 12;\n}')
    assert '2: static int foo ( )\n' in stdout
    assert '3: {\n' in stdout
    assert '4: return 12 ;' in stdout
    assert '5: }\n' in stdout

def test_tokens_function3(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nint x; void foo(){ x |= 1 << 30; }')
    assert '2: int x@var1 ; void foo ( ) { x@var1 |=@exprUNIQUE 1 <<@exprUNIQUE 30 ; }\n' in stdout

def test_tokens_for(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nint buf[10]; void foo() { for (int i:buf){} }')
    assert '2: int buf@var1 [ 10 ] ; void foo ( ) { for ( int i@var2 :@exprUNIQUE buf@var1 ) { } }' in stdout


def test_tokens_for_declarations(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(void) { for (int i = 0, j = 1, *p = &i; i < j; i++) {} }')
    assert '2: void f ( ) { for ( int i@var1 = 0 , j@var2 = 1 , * p@var3 =@exprUNIQUE &@exprUNIQUE i@var1 ;' in stdout


def test_tokens_location(tmp_path):
    # clang only writes the line when it differs from the previous location
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(void)\n{\n  int a = 1; int b = a;\n  int c;\n}')
    assert '4: int a@var1 = 1 ; int b@var2 =@exprUNIQUE a@var1 ;' in stdout
    assert '5: int c@var3 ;' in stdout


def test_tokens_location_macro(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '#define DECL(n) int n = 1\nvoid f(void)\n{\n  DECL(a);\n}')
    assert '4: int a@var1 = 1 ;' in stdout


def test_tokens_location_braces(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, 'struct S {\n  int m;\n};\nvoid f(int x)\n{\n  if (x)\n  {\n    x = 1 +\n        x;\n  }\n}')
    assert '3: } ;\n' in stdout
    assert '5: {\n' in stdout
    assert '7: {\n' in stdout
    assert '9: x@var2 ;\n' in stdout
    assert '10: }\n' in stdout
    assert '11: }\n' in stdout


def test_tokens_namespace(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nnamespace N { int v; }\nnamespace { int w; }\nusing namespace N;')
    assert '2: namespace N { int v@var1 ; }' in stdout
    assert '3: namespace { int w@var2 ; }' in stdout
    assert '4: using namespace N ;' in stdout


def test_tokens_qualified_names(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, 'enum class F { P, Q };\n'
                                            'namespace N { int v; int g(); namespace M { int w; } int h() { return v + M::w; } }\n'
                                            'int N::g() { return v; }\n'
                                            'int f() { return (int)F::Q + N::v + N::g(); }\n'
                                            'using namespace N;\n'
                                            'int k() { return v; }')
    assert 'int h ( ) { return v@var1 +@exprUNIQUE M ::@exprUNIQUE w@var2 ; }' in stdout
    assert '3: int N :: g ( ) { return v@var1 ; }' in stdout
    assert 'F ::@exprUNIQUE Q' in stdout
    assert 'N ::@exprUNIQUE v@var1' in stdout
    assert 'N :: g (' in stdout
    assert '6: int k ( ) { return v@var1 ; }' in stdout


def test_tokens_implicit_decls(tmp_path):
    # clang adds implicit typedefs and operator new/delete declarations
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, 'int x;')
    assert '1: int x@var1 ;\n' in stdout
    assert '__builtin_va_list' not in stdout
    assert 'operator' not in stdout


def test_tokens_goto_label(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(void) {\ngoto end;\nend:\nreturn;\nagain: { goto again; }\n}')
    assert '3: goto end ;' in stdout
    assert '4: end : ;' in stdout
    assert '6: again : ; { goto again ; }' in stdout


def test_symbol_database_label_block(tmpdir):
    __check_symbol_database(tmpdir, 'void f() { again: { int x; goto again; } }')


def test_tokens_array_init(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(void) { int a[2] = {1, 2}; int m[1][2] = {{1, 2}}; int *p = a; }')
    stdout = re.sub(r'@expr[0-9A-Z]+', '', stdout)
    assert '2: void f ( ) { int a@var1 [ 2 ] = { 1 , 2 } ; int m@var2 [ 1 ] [ 2 ] = { { 1 , 2 } } ; int * p@var3 = a@var1 ; }' in stdout


def test_tokens_implicit_members(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct S { int m; };\nS s1, s2 = s1;')
    assert '2: struct S { int m@var1 ; } ;' in stdout


def test_tokens_struct_anonymous(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nstruct { int a; } s;\nstruct O { struct { int b; } in; } o;')
    assert '2: struct Anonymous0 { int a@var1 ; } ; struct Anonymous0 s@var2 ;' in stdout
    assert '3: struct O { struct Anonymous1 { int b@var3 ; } ; struct Anonymous1 in@var4 ; } ; struct O o@var5 ;' in stdout


def test_symbol_database_struct_anonymous(tmp_path):
    for ext in ('c', 'cpp'):
        test_file = tmp_path / ('test.' + ext)
        with open(test_file, 'wt') as f:
            f.write('struct { int a; } s; struct O { struct { int b; } in; } o;\n')
        ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
        assert ret == 0, stdout
        assert 'mType: struct Anonymous0' in stdout
        assert 'mType: struct Anonymous1' in stdout


def test_tokens_typedef_anonymous(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\ntypedef struct { int x; } T;\ntypedef enum { A } E;\nT t;\nE e;')
    assert '2: struct T { int x@var1 ; } ;' in stdout
    assert '3: enum E { A } ;' in stdout
    assert ': typedef' not in stdout


def test_symbol_database_typedef_anonymous(tmp_path):
    for ext in ('c', 'cpp'):
        test_file = tmp_path / ('test.' + ext)
        with open(test_file, 'wt') as f:
            f.write('typedef struct { int x; } T; typedef enum { A } E; T t; E e;\n')
        ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
        assert ret == 0, stdout
        assert 'mType: struct T' in stdout
        assert 'mType: enum E' in stdout


def test_tokens_template1(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\ntemplate<class T> struct Foo {\nT x; };\nFoo<int> foo;\n')
    assert ': struct Foo<int> {' in stdout
    assert ': int x@var1 ;' in stdout
    assert ': Foo<int> foo@var2 ;' in stdout



def test_tokens_union(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nunion U { int i; float f; };\nunion U u;')
    assert '2: union U { int i@var1 ; float f@var2 ; } ;' in stdout


def test_symbol_database_union(tmp_path):
    for ext in ('c', 'cpp'):
        test_file = tmp_path / ('test.' + ext)
        with open(test_file, 'wt') as f:
            f.write('union U { int i; float f; };\n')
        ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
        assert ret == 0, stdout
        assert re.search(r'Scope: 0x[0-9a-f]+ Union', stdout), stdout
        assert not re.search(r'Scope: 0x[0-9a-f]+ (Struct|Class)', stdout), stdout


def test_tokens_const_method(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct C {\nint get() const { return 0; }\nint get2() const;\nint get3();\n};\nint C::get2() const { return 0; }')
    assert '3: int get ( ) const { return 0 ; }' in stdout
    assert '4: int get2 ( ) const ;' in stdout
    assert '5: int get3 ( ) ;' in stdout
    assert '7: int C :: get2 ( ) const { return 0 ; }' in stdout


def test_symbol_database_const_method(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct C { int get() const; int set(); };\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    funcs = re.findall(r'name: ([a-z]+) .*?isConst: (true|false)', stdout, re.DOTALL)
    assert ('get', 'true') in funcs, stdout
    assert ('set', 'false') in funcs, stdout


def test_tokens_implicit_this(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct C {\nint f() { return x + this->x; }\nvoid g() { f(); }\nint x;\n};')
    assert '3: int f ( ) { return x@var1 +@exprUNIQUE this .@exprUNIQUE x@var1 ; }' in stdout
    assert '4: void g ( ) { f (@exprUNIQUE ) ; }' in stdout


def test_ast_implicit_this(tmpdir):
    __check_ast(tmpdir, 'struct C { int f(); int x; }; int C::f() { return x + this->x; }')


def test_symbol_database_record_type_in_body(tmp_path):
    for ext in ('c', 'cpp'):
        test_file = tmp_path / ('test.' + ext)
        with open(test_file, 'wt') as f:
            if ext == 'c':
                f.write('struct C { struct C *next; };\n')
            else:
                f.write('struct C { void f(C *o) { C *p = o; } C *next; };\n')
        ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
        assert ret == 0, stdout
        assert 'mType: none' not in stdout, stdout


def test_ast_this_in_inline_method(tmpdir):
    __check_ast(tmpdir, 'struct C { int f() { return x + this->x; } int x; };')


def test_tokens_ctor_initializer_list(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct A { A() {} A(int) {} };\n'
                                            'struct D { D() {} D(int, int) {} };\n'
                                            'struct C : A {\n'
                                            'C(int a) : A(a), x(a+1), y{2}, d(1, 2) {}\n'
                                            'C() : A{2}, x(), d() {}\n'
                                            'C(int, int) : C() {}\n'
                                            'int x;\nint y = 3;\nD d;\nD d2;\n};')
    assert '5: C ( int a@var1 ) : A ( a@var1 ) , x@var2 ( a@var1 + 1 ) , y@var3 { 2 } , d@var4 ( 1 , 2 ) { }' in stdout
    assert '6: C ( ) : A { 2 } , x@var2 ( ) , d@var4 ( ) { }' in stdout
    assert '7: C ( int , int ) : C ( ) { }' in stdout


def test_tokens_ctor_initializer_param(tmp_path):
    # parameter in initializer list is not qualified
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct D { D(int a) : v(a) {} int v; };')
    assert '2: struct D { D ( int a@var1 ) : v@var2 ( a@var1 ) { } int v@var2 ; } ;' in stdout


def test_ast_ctor_initializer_list(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct C { C(int a) : x(a), y{2} {} int x; int y; };\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    assert "(\n|-x 'signed int'\n`-a 'signed int'\n" in stdout
    assert "{\n|-y 'signed int'\n`-2 'signed int'\n" in stdout


def test_tokens_base_classes(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nnamespace N { struct B {}; }\nstruct A {};\n'
                                            'class C : public A, protected virtual N::B {};\nstruct D : C {};')
    assert '4: class C : public A , protected virtual N :: B { } ;' in stdout
    assert '5: struct D : C { } ;' in stdout


def test_symbol_database_base_classes(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('namespace N { struct B {}; }\nstruct A {};\n'
                'class C : public A, protected virtual N::B {};\nstruct D : C {};\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    assert re.search(r'derivedFrom\[2\] = \( Public 0x[0-9a-f]+ A,Virtual  Protected 0x[0-9a-f]+ B \)', stdout), stdout
    assert re.search(r'derivedFrom\[1\] = \( Public 0x[0-9a-f]+ C \)', stdout), stdout


def test_tokens_definition_after_declaration(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nint g(int);\nint g(int b) { return b; }\nint h(int c);\nint h(int d) { return d; }')
    assert '3: int g ( int b@var1 ) { return b@var1 ; }' in stdout
    assert '4: int h ( int c@var2 ) ;' in stdout
    assert '5: int h ( int d@var3 ) { return d@var3 ; }' in stdout


def test_symbol_database_definition_after_declaration(tmpdir):
    __check_symbol_database(tmpdir, 'struct C { int f(int a); }; int C::f(int a) { return a + 1; } int g(int); int g(int b) { return b; }')


def test_tokens_direct_init(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct S { S(); S(int, int); };\nvoid f() {\nS s1;\nS s2(s1);\nS s3(1, 2);\nS s4{1, 2};\nint i(3);\nint j{4};\n}')
    assert '4: S s1@var1 ;' in stdout
    assert '5: S s2@var2 (@exprUNIQUE s1@var1 ) ;' in stdout
    assert '6: S s3@var3 (@exprUNIQUE 1 ,@expr' in stdout
    assert '7: S s4@var4 {@exprUNIQUE 1 ,@expr' in stdout
    assert '8: int i@var5 (@exprUNIQUE 3 ) ;' in stdout
    assert '9: int j@var6 {@exprUNIQUE 4 } ;' in stdout


def test_ast_direct_init(tmpdir):
    __check_ast(tmpdir, 'struct S { int a; int b; };\nvoid f() { S s1; S s2(s1); S s4{1, 2}; int i(3); int j{4}; }')


def test_tokens_member_varid(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nstruct A { int c; };\nstruct B { struct A a; struct A a2; };\n'
                                            'void f(struct B *p) {\nstruct B b;\nb.a.c = 1;\nb.a2.c = b.a.c;\np->a.c = 0;\n}')
    stdout = re.sub(r'@expr[0-9A-Z]+', '', stdout)
    assert '6: b@var5 . a@var6 . c@var7 = 1 ;' in stdout
    assert '7: b@var5 . a2@var8 . c@var9 = b@var5 . a@var6 . c@var7 ;' in stdout
    assert '8: p@var4 . a@var10 . c@var11 = 0 ;' in stdout


def test_symbol_database_member_varid(tmpdir):
    __check_symbol_database(tmpdir, 'struct S { int x; int y; }; void f() { S s; S *p; s.x = 1; p->y = s.x; }')


def test_uninitvar_member(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('struct S { int x; };\nint f(void) { struct S s; return s.x; }\n')
    _, _, stderr = cppcheck(['-q', '--clang', '--template={line}:{column}:{id}', str(test_file)])
    assert '2:36:uninitvar' in stderr


def test_uninit_member_var(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct C {\n    C() : x(0) {}\n    C(const C &o) : x(o.x), y(o.y) {}\n    int x;\n    int y;\n};\n')
    _, _, stderr = cppcheck(['-q', '--clang', '--enable=warning', '--template={line}:{column}:{id}:{message}', str(test_file)])
    assert stderr == "2:5:uninitMemberVar:Member variable 'C::y' is not initialized in the constructor.\n"


def test_uninit_struct_member(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('struct S { int x; };\nint f(void) { struct S s; return s.x; }\n')
    _, _, stderr = cppcheck(['-q', '--clang', '--template={line}:{column}:{id}', str(test_file)])
    assert '2:34:uninitStructMember' in stderr


def test_symbol_database_copy_constructor(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct C { C(); C(const C &o); C(C &&o); };\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    assert 'type: CopyConstructor' in stdout
    assert 'type: MoveConstructor' in stdout


def test_tokens_default_member_init(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct C {\nint z = 3;\nint w{4};\nint a[2] = {1, 2};\nint v;\n};\nC c{};')
    assert '3: int z@var1 = 3 ;' in stdout
    assert '4: int w@var2 { 4 } ;' in stdout
    assert '5: int a@var3 [ 2 ] = { 1 , 2 } ;' in stdout
    assert '6: int v@var4 ;' in stdout
    assert '8: C c@var5 { } ;' in stdout


def test_tokens_init_list_implicit_values(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nstruct S { int a; int b; };\nstruct S s = {1};\nint a[3] = {1};')
    assert '3: struct S s@var3 = { 1 } ;' in stdout
    assert '4: int a@var4 [ 3 ] = { 1 } ;' in stdout


def test_uninit_member_var_default_init(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct C {\n    C() {}\n    int z = 3;\n    int w{4};\n    int v;\n};\n')
    _, _, stderr = cppcheck(['-q', '--clang', '--enable=warning', '--template={line}:{id}:{message}', str(test_file)])
    assert stderr == "2:uninitMemberVar:Member variable 'C::v' is not initialized in the constructor.\n"


def test_tokens_nested_type(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct S {\nstruct N { int a; };\nN n;\nvoid f(N *p);\n};\nS::N g;\nvoid S::f(N *p) { N local; }')
    assert '4: N n@var2 ;' in stdout
    assert '7: S :: N g@var4 ;' in stdout
    assert '8: void S :: f ( N * p@var5 ) { N local@var6 ; }' in stdout


def test_symbol_database_nested_type(tmpdir):
    __check_symbol_database(tmpdir, 'struct S { struct N { int a; }; N n; void f(N *p); }; S::N g; void S::f(N *p) { N local; }')


def test_tokens_function_pointer(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nint g(int x) { return x; }\nvoid f() {\n'
                                            'int (*fp)(int) = g;\n'
                                            'for (int i = 0, (*q)(int) = g; i < 2; i++) { q(i); }\n'
                                            'int (*fa[3])(int);\nint a[3];\nint (*pa)[3] = &a;\nint (&ra)[3] = a;\n}')
    stdout = re.sub(r'@expr[0-9A-Z]+', '', stdout)
    assert '4: int ( * fp@var2 ) ( int ) = g ;' in stdout
    assert '5: for ( int i@var3 = 0 , ( * q@var4 ) ( int ) = g ; i@var3 < 2 ; i@var3 ++ ) { q@var4 ( i@var3 ) ; }' in stdout
    assert '6: int ( * fa@var5 [ 3 ] ) ( int ) ;' in stdout
    assert '8: int ( * pa@var7 ) [ 3 ] = & a@var6 ;' in stdout
    assert '9: int ( & ra@var8 ) [ 3 ] = a@var6 ;' in stdout


def test_symbol_database_function_pointer(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('int g(int x) { return x; }\nint (*fp)(int) = g;\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    fp = stdout[stdout.find('mNameToken: fp'):]
    assert 'isPointer: true' in fp[:fp.find('valueType')]
    assert 'signed int *' in fp


def test_tokens_access_specifier(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nclass C {\npublic:\nint a;\nprotected:\nint b;\nprivate:\nint c;\n};')
    assert '3: public:\n' in stdout
    assert '5: protected:\n' in stdout
    assert '7: private:\n' in stdout


def test_tokens_case_label(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(int x) {\nswitch (x) {\ncase 1:\nx = 5;\nbreak;\ndefault:\nbreak;\n}\n}')
    assert '4: case 1 : ;' in stdout
    assert '7: default : ;' in stdout


def test_ast_case_label(tmpdir):
    __check_ast(tmpdir, 'void f(int x) { switch (x) { case 1: x = 5; break; default: break; } }')


def test_tokens_added_braces(tmp_path):
    test_file = tmp_path / 'test.c'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(int x) {\nif (x)\nx = 1;\nwhile (x)\nx--;\n}')
    stdout = re.sub(r'@[a-zA-Z0-9]+', '', stdout)
    assert '3: if ( x ) {\n4: x = 1 ; }' in stdout
    assert '5: while ( x ) {\n6: x -- ; }' in stdout


def test_tokens_elaborated_type(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nunion U { int i; };\nstruct S { int a; };\nenum E { A };\nunion U u;\nstruct S s;\nS s2;\nenum E e;')
    assert '5: union U u@var3 ;' in stdout
    assert '6: struct S s@var4 ;' in stdout
    assert '7: S s2@var5 ;' in stdout
    assert '8: enum E e@var6 ;' in stdout


def test_symbol_database_elaborated_type(tmpdir):
    __check_symbol_database(tmpdir, 'union U { int i; }; struct S { int a; }; enum E { A }; union U u; struct S s; S s2; enum E e;')


def test_tokens_function_pointer_parameter(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nvoid f(int (*cb)(int), int (*)(int), int (&r)[2]);')
    assert '2: void f ( int ( * cb@var1 ) ( int ) , int ( * ) ( int ) , int ( & r@var2 ) [ 2 ] ) ;' in stdout


def test_ast_array_to_pointer(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('void f(void) {\n    char buf[10];\n    char *p = buf;\n    char *q = &buf[1];\n}\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    assert "`-buf 'char *'" in stdout
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug', str(test_file)])
    assert ret == 0, stdout
    assert 'lifetime[Address]=(buf)' in stdout


def test_tokens_inline(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\ninline int f() { return 0; }\nstatic inline int g() { return 1; }')
    assert '2: int f ( ) { return 0 ; }' in stdout
    assert '3: static int g ( ) { return 1 ; }' in stdout


def test_symbol_database_inline(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('inline int f() { return 0; }\nstruct S { int m() { return 2; } inline int n(); };\nint S::n() { return 3; }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    funcs = re.findall(r'name: ([a-z]+) .*?isInline: (true|false)', stdout, re.DOTALL)
    assert funcs == [('f', 'true'), ('m', 'true'), ('n', 'false')], stdout
    ret, stdout, _ = cppcheck(['-q', '--clang', '--dump', str(test_file)])
    assert ret == 0, stdout
    with open(str(test_file) + '.dump', 'rt') as f:
        dump = f.read()
    assert dump.count('isInlineKeyword="true"') == 2, dump


def test_tokens_default_delete(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct C {\nC() = default;\nC(const C &) = delete;\n};\nstruct D { D(); };\nD::D() = default;\nvoid f(int) = delete;')
    assert '3: C ( ) = default ;' in stdout
    assert '4: C ( const C & ) = delete ;' in stdout
    assert '7: D :: D ( ) = default ;' in stdout
    assert '8: void f ( int ) = delete ;' in stdout


def test_symbol_database_default_delete(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct C { C() = default; C(const C &) = delete; };\nstruct D { D(); };\nD::D() = default;\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    funcs = re.findall(r'name: ([A-Z]) .*?hasBody: (true|false).*?isDefault: (true|false)\n\s+isDelete: (true|false)', stdout, re.DOTALL)
    assert funcs == [('C', 'false', 'true', 'false'), ('C', 'false', 'false', 'true'), ('D', 'false', 'true', 'false')], stdout


def test_tokens_template_member_out_of_line(tmp_path):
    # the template definition is not imported, only the instantiation
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\ntemplate<class T> struct A {\nT x;\nT get();\n};\n'
                                            'template<class T> T A<T>::get() { return x; }\n'
                                            'int main() { A<int> a; return a.get(); }')
    assert 'int get ( ) { return x@var1 ; }' in stdout
    assert 'T get' not in stdout


def test_tokens_new_delete(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct S { S(); S(int); };\nvoid g(int n) {\n'
                                            'int *p = new int[3];\nint *q = new int(4);\nint *r = new int;\n'
                                            'S *s = new S(1);\nS *t = new S[n];\nint *u = new int[2]{1, 2};\nS *v = new S();\n'
                                            'delete[] p;\ndelete q;\n}')
    stdout = re.sub(r'@expr[0-9A-Z]+', '', stdout)
    assert '4: int * p@var2 = new int [ 3 ] ;' in stdout
    assert '5: int * q@var3 = new int ( 4 ) ;' in stdout
    assert '6: int * r@var4 = new int ;' in stdout
    assert '7: S * s@var5 = new S ( 1 ) ;' in stdout
    assert '8: S * t@var6 = new S [ n@var1 ] ;' in stdout
    assert '9: int * u@var7 = new int [ 2 ] { 1 , 2 } ;' in stdout
    assert '10: S * v@var8 = new S ( ) ;' in stdout
    assert '11: delete [ ] p@var2 ;' in stdout
    assert '12: delete q@var3 ;' in stdout


def test_ast_new_delete(tmpdir):
    __check_ast(tmpdir, 'void g(int n) { int *p; p = new int[n]; int *q; q = new int(4); int *u; u = new int[2]{1, 2}; delete[] p; delete q; }')


def test_tokens_cxx_casts(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct B { virtual ~B(); };\nstruct D : B {};\nvoid f(double d, B *b) {\n'
                                            'int x = static_cast<int>(d);\nint y = int(d);\n'
                                            'long z = reinterpret_cast<long>(&d);\nconst double *c = &d;\n'
                                            'double *m = const_cast<double *>(c);\nD *p = dynamic_cast<D *>(b);\nint w = int{3};\n}')
    stdout = re.sub(r'@[a-zA-Z0-9]+', '', stdout)
    assert '5: int x = static_cast < int > ( d ) ;' in stdout
    assert '6: int y = int ( d ) ;' in stdout
    assert '7: long z = reinterpret_cast < long > ( & d ) ;' in stdout
    assert '9: double * m = const_cast < double * > ( c ) ;' in stdout
    assert '10: D * p = dynamic_cast < D * > ( b ) ;' in stdout
    assert '11: int w = int { 3 } ;' in stdout


def test_ast_cxx_casts(tmpdir):
    __check_ast(tmpdir, 'void f(double d, const double *c) { int x; x = static_cast<int>(d); x = int(d); x = int{3}; long z; z = reinterpret_cast<long>(&d); double *m; m = const_cast<double *>(c); }')


def test_ast_sizeof(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('int x[4];\nvoid f(void) {\n    int a;\n    a = sizeof(int);\n    a = sizeof(x[0]);\n}\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    # the operand of sizeof is the expression, the sizeof keyword has no type
    assert "`-( 'unsigned long'\n  |-sizeof\n  `-int 'signed int'\n" in stdout
    assert "`-( 'unsigned long'\n  |-sizeof\n  `-[ 'signed int'\n" in stdout


def test_tokens_try_catch(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nint f(int x) {\ntry { throw 1; }\ncatch (int e) { x = e; }\ncatch (...) { throw; }\nreturn x;\n}')
    stdout = re.sub(r'@expr[0-9A-Z]+', '', stdout)
    assert '3: try { throw 1 ; }' in stdout
    assert '4: catch ( int e@var2 ) { x@var1 = e@var2 ; }' in stdout
    assert '5: catch ( ... ) { throw ; }' in stdout


def test_symbol_database_try_catch(tmpdir):
    __check_symbol_database(tmpdir, 'int f(int x) { try { throw 1; } catch (int e) { x = e; } catch (...) { throw; } return x; }')


def test_ast_try_catch(tmpdir):
    __check_ast(tmpdir, 'int f(int x) { try { throw 1; } catch (int e) { x = e; } catch (...) { throw; } return x; }')


def test_ast_init_list(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('void f(void) { int b[2][2] = {{1, 2}, {3}}; }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    # the elements are the operand of "{"
    assert "`-{\n  `-,\n    |-{\n    | `-,\n    | | |-1 'signed int'\n    | | `-2 'signed int'\n    `-{\n      `-3 'signed int'\n" in stdout


def test_ast_array_value_type(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('void f() {\n    int a[3];\n    int m[2][2];\n    a[0] = 1;\n    m[1][1] = 2;\n    int (&ra)[3] = a;\n}\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    # arrays have pointer value types like in the normal import
    assert "|-a 'signed int *'" in stdout
    assert "|-m 'signed int * *'" in stdout
    assert "|-ra 'signed int *'" in stdout
    _, _, stderr = cppcheck(['-q', '--clang', '--enable=all', '--template={id}', str(test_file)])
    assert 'AssignmentAddressToInteger' not in stderr


def test_tokens_virtual(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct B {\nvirtual ~B();\nvirtual void f() = 0;\nvirtual int g() const;\n};\n'
                                            'struct D : B {\nvoid f() override;\nint g() const final;\n};\nB::~B() {}')
    assert '3: virtual ~ B ( ) ;' in stdout
    assert '4: virtual void f ( ) = 0 ;' in stdout
    assert '5: virtual int g ( ) const ;' in stdout
    assert '8: void f ( ) override ;' in stdout
    assert '9: int g ( ) const final ;' in stdout
    assert '11: B :: ~ B ( ) { }' in stdout


def test_symbol_database_virtual(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct B { virtual ~B(); virtual void f() = 0; };\nstruct D : B { void f() override; };\nstruct E : B { void f() final; };\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    funcs = re.findall(r'name: (\w+) .*?type: (\w+).*?hasVirtualSpecifier: (\w+)\n\s+isPure: (\w+).*?hasOverrideSpecifier: (\w+)\n\s+hasFinalSpecifier: (\w+)', stdout, re.DOTALL)
    assert funcs == [('B', 'Destructor', 'true', 'false', 'false', 'false'),
                     ('f', 'Function', 'true', 'true', 'false', 'false'),
                     ('f', 'Function', 'false', 'false', 'true', 'false'),
                     ('f', 'Function', 'false', 'false', 'false', 'true')], stdout


def test_tokens_operator_call(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nstruct V {\nV operator+(const V &o) const;\nV &operator=(const V &o);\n'
                                            'V &operator++();\nV operator++(int);\nbool operator!() const;\n'
                                            'int operator[](int i) const;\nint operator()(int a, int b) const;\n};\n'
                                            'bool operator==(const V &a, const V &b);\n'
                                            'void f(V a, V b) {\nV c = a + b;\nc = a;\n++c;\nc++;\nbool n = !c;\n'
                                            'int i = c[2];\nint j = c(1, 2);\nbool e = a == b;\n}')
    stdout = re.sub(r'@[a-zA-Z0-9]+', '', stdout)
    assert '13: V c = a + b ;' in stdout
    assert '14: c = a ;' in stdout
    assert '15: ++ c ;' in stdout
    assert '16: c ++ ;' in stdout
    assert '17: bool n = ! c ;' in stdout
    assert '18: int i = c [ 2 ] ;' in stdout
    assert '19: int j = c . operator() ( 1 , 2 ) ;' in stdout
    assert '20: bool e = a == b ;' in stdout


def test_ast_variable_value_type(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('struct V { int x; int get() const { return x; } };\n'
                'int f(const V &o, int (*cb)(int)) { return o.x + cb(1); }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    # variables get the declared type, like in the normal import
    assert "`-x 'signed int'" in stdout
    assert "|-o 'const V &'" in stdout
    assert "|-cb 'signed int *'" in stdout


def test_tokens_lambda(tmp_path):
    test_file = tmp_path / 'test.cpp'
    stdout = _run_cppcheck_debug(test_file, '\nint f(int n) {\nauto lam = [&n](int k) { return n + k; };\nauto g = [n]() { return n; };\nreturn lam(1) + g();\n}')
    stdout = re.sub(r'@expr[0-9A-Z]+', '', stdout)
    assert '3: auto lam@var2 = [ & n@var1 ] ( int k@var3 ) { return n@var1 + k@var3 ; } ;' in stdout
    assert '4: auto g@var4 = [ n@var1 ] ( ) { return n@var1 ; } ;' in stdout
    assert '5: return lam@var2 ( 1 ) + g@var4 ( ) ;' in stdout


def test_symbol_database_lambda(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('int f(int n) { auto lam = [&n](int k) { return n + k; }; return lam(1); }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-symdb', str(test_file)])
    assert ret == 0, stdout
    assert re.search(r'Scope: 0x[0-9a-f]+ Lambda', stdout), stdout
    assert re.search(r'mScope: Lambda \[', stdout), stdout


def test_ast_lambda(tmp_path):
    test_file = tmp_path / 'test.cpp'
    with open(test_file, 'wt') as f:
        f.write('int f(int n) { auto lam = [&n](int k) { return n + k; }; return lam(1); }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    # "[" => "(" => "{", the captures are the second operand of "["
    assert re.search(r"`-\[ f:0x[0-9a-f]+\n  \|-\( 'signed int'\n  \| `-\{\n  `-&\n    `-n 'signed int'", stdout), stdout


def test_ast_function_name_value_type(tmp_path):
    test_file = tmp_path / 'test.c'
    with open(test_file, 'wt') as f:
        f.write('int g(int x) { return x; }\nvoid f(void) { int (*fp)(int); fp = g; }\n')
    ret, stdout, _ = cppcheck(['-q', '--clang', '--debug-ast', str(test_file)])
    assert ret == 0, stdout
    # a function name has no value type, like in the normal import
    assert re.search(r"`-g f:0x[0-9a-f]+\n", stdout), stdout
