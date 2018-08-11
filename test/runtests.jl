using Glob
using Test

macro test_types(arr, types)
    return quote
        @test length($arr) == length($types)
        for i in 1:length($arr)
            @test isa($arr[i], $types[i])
        end
    end
end

# various unit tests, in no particular order

@test !occursin(fn"abc*", "ABXABXAB")
@test occursin(fn"AB*AB*AB", "ABXABXAB")
@test occursin(fn"AB*AB*AB", "ABXABAB")
@test !occursin(fn"AB*AB*AB", "AABAB")
@test occursin(fn"AB*AB*AB", "ABABAB")
@test occursin(fn"AB*AB*B", "ABABAB")
@test occursin(fn"AB*AB*", "ABABAB")
@test occursin(fn"AB*AB*??", "ABABAB")
@test !occursin(fn"AB*AB*???", "ABABAB")
@test occursin(fn"AB*AB*??***", "ABABAB")
@test occursin(fn"AB*AB*??***", "ABABABC")
@test occursin(fn"AB*AB*??***", "ABABABCDEFG")
@test occursin(fn"?AB*AB*??***", ".ABABABCDEFG")
@test !occursin(fn"?AB*AB*??***"p, ".ABABABCDEFG")
@test_throws ErrorException Glob.FilenameMatch("?AB*AB*??***","z")
@test occursin(fn"[abc]", "a")
@test !occursin(fn"[abc]", "A")
@test occursin(fn"[abc]"i, "A")
@test occursin(fn"[abc]", "b")
@test occursin(fn"[abc]", "c")
@test !occursin(fn"[abc]", "x")
@test !occursin(fn"[a-d]", "x")
@test occursin(fn"[a-d]", "a")
@test occursin(fn"[a-d]", "d")
@test !occursin(fn"[a--]", "e")
@test occursin(fn"[--e]", "e")
@test !occursin(fn"[f-e]", "e")
@test !occursin(fn"[g-e]", "e")
@test !occursin(fn"[g-f]", "e")
@test occursin(fn"[a-f]", "e")
@test occursin(fn"[a-e]", "e")
@test occursin(fn"[f-ee]", "e")
@test !occursin(fn"[A-Z]", "e")
@test occursin(fn"[A-z]", "e")
@test occursin(fn"[\]", "\\")
@test_throws ErrorException occursin(fn"[[:a:]]", "e")
@test_throws ErrorException !occursin(fn"[\[:a:]]", "e")
@test !occursin(fn"[\[:a:]]"x, "e")
@test_throws ErrorException occursin(fn"[\\[:a:]]", "e")
@test occursin(fn"[\[:a-e:]]"x, "e]")
@test occursin(fn"[\[:a-e:]"x, "e")
@test !occursin(fn"[\[:a-e:xxxx"x, "e")
@test occursin(fn"[\[:a-e:xxxx-]"x, "e")
@test occursin(fn"[a-]", "a")
@test occursin(fn"[a-]", "-")
@test !occursin(fn"[a-]", "b")
@test occursin(fn"[!a-]", "b")
@test !occursin(fn"[!a-]", "a")
@test occursin(fn"[!a]", "!")
@test !occursin(fn"[!!]", "!")
@test !occursin(fn"[!a]", "a")
@test occursin(fn"[!a]", "b")
@test !occursin(fn"[][]", "")
@test occursin(fn"[]", "[]")
@test occursin(fn"[][]", "[")
@test occursin(fn"[][]", "]")
@test !occursin(fn"[][]", "x")
@test !occursin(fn"[]-[]", "x")
@test !occursin(fn"[]-[]", "-")
@test !occursin(fn"[]-[]", "\\")
@test occursin(fn"[\[-\]]*"x, "][")
@test occursin(fn"[\]]*"x, "][")
@test occursin(fn"[\[-\]]*"x, "][")
@test occursin(fn"[[-\]]*"x, "][")
@test occursin(fn"base/[\[-\]]*"dpx,"base/][x")
@test occursin(fn"[\[-\]]"x, "\\")
@test occursin(fn"[[-\]]"x, "\\")
@test occursin(fn"[---]", "-")
@test !occursin(fn"[!---]", "-")
@test occursin(fn"[!---]", "0")
@test !occursin(fn"[---a-zA-Z]", "0")
@test !occursin(fn"[---a-zA-Z:]", "0")
@test !occursin(fn"[---!]", "0")
@test occursin(fn"[---!]", "!")
@test !occursin(fn"[---!]", "a")
@test !occursin(fn"[---!]", "\0")
@test occursin(fn"ab/c/d"dp, "ab/c/d")
@test !occursin(fn"ab/c/d"dp, "ab/c?d")
@test !occursin(fn"ab/./d"dp, "ab/?/d")
@test !occursin(fn"ab*d"dp, "aba/d")
@test !occursin(fn"ab*d"dp, "ab/d")
@test occursin(fn"ab*d", "ab/d")
@test occursin(fn"ab*d", "aba/d")
@test occursin(fn"[a-z]"i, "B")
@test !occursin(fn"[a-z]"i, "_")
@test occursin(fn"[A-z]"i, "_")
@test !occursin(fn"[a-Z]"i, "_")
@test !occursin(fn"#[a-Z]%"i, "#a%")
@test occursin(fn"#[α-ω]%"i, "#Γ%")
@test !occursin(fn"#[α-ω]%", "#Γ%")
@test occursin(fn"#[α-ω]%", "#γ%")
@test !occursin(fn"a?b"d, "a/b")
@test occursin(fn"a?b", "a/b")
@test !occursin(fn"?b"p, ".b")
@test occursin(fn"?b", ".b")
@test occursin(fn"?/?b", "./.b")
@test !occursin(fn"?/?b"p, "./.b")
@test occursin(fn"./?b"p, "./.b")
@test !occursin(fn"./?b"pd, "./.b")
@test occursin(fn"./.b"pd, "./.b")
@test !occursin(fn"?/.b"pd, "./.b")
@test occursin(fn"""./.b"""pd, "./.b")
@test !occursin(fn"""?/.b"""pd, "./.b")
@test occursin(fn"_[[:blank:][.a.]-c]_", "_b_")
@test !occursin(fn"_[[:blank:][.a.]-c]_", "_-_")
@test occursin(fn"_[[:blank:][.a.]-c]_", "_ _")
@test occursin(fn"_[[:alnum:]]_", "_a_")
@test !occursin(fn"_[[:alnum:]]_", "_[_")
@test !occursin(fn"_[[:alnum:]]_", "_]_")
@test !occursin(fn"_[[:alnum:]]_", "_:_")
@test occursin(fn"_[[:alpha:]]_", "_z_")
@test !occursin(fn"_[[:alpha:]]_", "_[_")
@test occursin(fn"_[[:cntrl:]]_", "_\0_")
@test occursin(fn"_[[:cntrl:]]_", "_\b_")
@test !occursin(fn"_[[:cntrl:]]_", "_:_")
@test !occursin(fn"_[[:cntrl:]]_", "_ _")
@test occursin(fn"_[[:digit:]]_", "_0_")
@test !occursin(fn"_[[:digit:]]_", "_:_")
@test occursin(fn"_[[:graph:]]_", "_._")
@test !occursin(fn"_[[:graph:]]_", "_ _")
@test occursin(fn"_[[:lower:]]_", "_a_")
@test occursin(fn"_[[:lower:]]_"i, "_A_")
@test !occursin(fn"_[[:lower:]]_", "_A_")
@test !occursin(fn"_[[:lower:]]_", "_:_")
@test occursin(fn"_[[:print:]]_", "_a_")
@test !occursin(fn"_[[:print:]]_", "_\7_")
@test occursin(fn"_[[:punct:]]_", "_:_")
@test !occursin(fn"_[[:punct:]]_", "_p_")
@test occursin(fn"_[[:space:]]_", "_\f_")
@test !occursin(fn"_[[:space:]]_", "_:_")
@test !occursin(fn"_[[:space:]]_", "_\r\n_")
@test occursin(fn"_[[:upper:]]_", "_A_")
@test occursin(fn"_[[:upper:]]_"i, "_a_")
@test !occursin(fn"_[[:upper:]]_", "_a_")
@test !occursin(fn"_[[:upper:]]_", "_:_")
@test occursin(fn"_[[:xdigit:]]_", "_a_")
@test !occursin(fn"_[[:xdigit:]]_", "_:_")
@test occursin(fn"_[[.a.]-[.z.]]_", "_c_")
@test !occursin(fn"_[[.a.]-[.z.]]_", "_-_")
@test !occursin(fn"_[[.a.]-[.z.]]_", "_]_")
@test !occursin(fn"_[[.a.]-[.z.]]_", "_[_")
@test occursin(fn"_[[=a=]]_", "_a_")
@test !occursin(fn"_[[=a=]]_", "_=_")
@test !occursin(fn"_[[=a=]]_", "_á_")
@test occursin(fn"[[=a=]-z]", "-")
@test_throws ErrorException occursin(fn"[a-[=z=]]", "e")

@test !occursin(fn"\?", "\\?")
@test occursin(fn"\?", "?")
@test occursin(fn"\?"e, "\\!")
@test !occursin(fn"\?"e, "?")

@test_types glob"ab/?/d".pattern (AbstractString, Glob.FilenameMatch, AbstractString)
@test_types glob"""ab/*/d""".pattern (AbstractString, Glob.FilenameMatch, AbstractString)
@test length(glob"ab/[/d".pattern) == 3
@test length(glob"ab/[/]d".pattern) == 3
@test_types glob"ab/[/]d".pattern (AbstractString, AbstractString, AbstractString)
@test_types glob"ab/[/d".pattern (AbstractString, AbstractString, AbstractString)
@test_types glob"ab/[]/d".pattern (AbstractString, AbstractString, AbstractString)
@test_types glob"ab/[]]/d".pattern (AbstractString, Glob.FilenameMatch, AbstractString)

@test glob("*") == filter(x->!startswith(x,'.'), readdir()) == readdir(glob"*")
@test glob(".*") == filter(x->startswith(x,'.'), readdir()) == readdir(glob".*")
@test isempty(Glob.glob("[.]*"))
@test glob([r".*"]) == readdir()
@test glob([".", r".*"]) == map(x->joinpath(".",x), readdir())
@test all([!startswith(x,'.') for x in Glob.glob("*.*")])

function test_string(x1)
    @static if VERSION < v"0.7.0-DEV.2437"
        x2 = string(eval(parse(x1)))
    else
        x2 = string(eval(Meta.parse(x1)))
    end
    x1 == x2 ? nothing : error(string(
        "string test failed:",
        "\noriginal: ", x1,
        "\n\nstringify: ", x2))
end

test_string("""Glob.GlobMatch(Any["base", r"h\\.+"])""")
test_string("""glob"base/*/a/[b]\"""")
test_string("""fn"base/*/a/[b]\"ipedx""")
test_string("""fn"base/*/a/[b]\"""")

@test_throws ErrorException Glob.GlobMatch("")
@test_throws ErrorException Glob.GlobMatch("/a/b/c")
