__precompile__()

module Glob

import Base: readdir, show, occursin, filter, filter!

export glob, @fn_str, @fn_mstr, @glob_str, @glob_mstr

if VERSION >= v"1.11"
    Base.include_string(Glob,
        """
        public FilenameMatch, GlobMatch, GlobStar
        public CASELESS, PERIOD, NOESCAPE, PATHNAME, EXTENDED
        """,
        @__FILE__)
end

@static if VERSION < v"1.7"
macro something(args...)
    noth = GlobalRef(Base, :nothing)
    something = GlobalRef(Base, :something)
    expr = :($something($noth))
    for arg in reverse(args)
        val = gensym()
        expr = quote
            $val = $(esc(arg))
            if $val === $noth
                $expr
            else
                $something($val)
            end
        end
    end
    return expr
end
end

const CASELESS = UInt32(1 << 0) # i -- Do case-insensitive matching
const PERIOD   = UInt32(1 << 1) # p -- A leading period (.) character must be exactly matched by a period (.) character
const NOESCAPE = UInt32(1 << 2) # e -- Do not treat backslash (\) as a special character
const PATHNAME = UInt32(1 << 3) # d -- Slash (/) character must be exactly matched by a slash (/) character
const EXTENDED = UInt32(1 << 4) # x -- Support extended (bash-like) features

struct FilenameMatch{S<:AbstractString}
    pattern::S
    options::UInt32
    FilenameMatch{S}(pattern, options) where {S} = new{S}(pattern, options)
end
function FilenameMatch(pattern::S, options::Integer=0) where {S<:AbstractString}
    return FilenameMatch{S}(pattern, options)
end
function FilenameMatch(pattern::AbstractString, flags::AbstractString)
    options = 0
    for f in flags
        options |= (f == 'i') ? CASELESS :
                   (f == 'p') ? PERIOD   :
                   (f == 'e') ? NOESCAPE :
                   (f == 'd') ? PATHNAME :
                   (f == 'x') ? EXTENDED :
                   error("unknown Filename Matcher flag: $f")
    end
    return FilenameMatch(pattern, options)
end

"""
    fn"pattern"ipedx

Returns a `Glob.FilenameMatch` object, which can be used with `occursin()`. Available flags are:

* `i` = `CASELESS` : Performs case-insensitive matching
* `p` = `PERIOD` : A leading period (`.`) character must be exactly matched by a period (`.`) character (not a `?`, `*`, or `[]`). A leading period is a period at the beginning of a string, or a period after a slash if PATHNAME is true.
* `e` = `NOESCAPE` : Do not treat backslash (`\`) as a special character (in extended mode, this only outside of `[]`)
* `d` = `PATHNAME` : A slash (`/`) character must be exactly matched by a slash (`/`) character (not a `?`, `*`, or `[]`), "**/" matches zero or more directories (globstar)
* `x` = `EXTENDED` : Additional features borrowed from newer shells, such as `bash` and `tcsh`
    * Backslash (`\``) characters in `[]` groups escape the next character
"""
(macro fn_str end, macro fn_mstr end, FilenameMatch)

macro fn_str(pattern, flags...) FilenameMatch(pattern, flags...) end
macro fn_mstr(pattern, flags...) FilenameMatch(pattern, flags...) end

function show(io::IO, fn::FilenameMatch)
    print(io, "fn\"", fn.pattern, '"')
    (fn.options & CASELESS) != 0 && print(io, 'i')
    (fn.options & PERIOD  ) != 0 && print(io, 'p')
    (fn.options & NOESCAPE) != 0 && print(io, 'e')
    (fn.options & PATHNAME) != 0 && print(io, 'd')
    (fn.options & EXTENDED) != 0 && print(io, 'x')
    nothing
end

function skip_to_slash(s::AbstractString, i)
    while true
        nc = iterate(s, i)
        nc === nothing && return nothing
        c, i = nc
        c == '/' && return i
    end
end

function occursin(fn::FilenameMatch, s::AbstractString)
    pattern = fn.pattern
    caseless = (fn.options & CASELESS) != 0
    periodfl = (fn.options & PERIOD  ) != 0
    noescape = (fn.options & NOESCAPE) != 0
    pathname = (fn.options & PATHNAME) != 0
    extended = (fn.options & EXTENDED) != 0

    mi = firstindex(pattern) # current index into pattern
    i = firstindex(s) # current index into s
    starmatch = i
    star = 0
    globstarmatch = 0  # Track globstar match position for directory-level backtracking
    globstar_mi = 0    # Pattern index after globstar
    globstar_star = 0  # Saved star state when entering globstar
    globstar_starmatch = i  # Saved starmatch state when entering globstar
    period = periodfl
    after_slash = true  # Track if previous pattern char was '/' (or at start)
    while true
        matchnext = iterate(s, i)
        matchnext === nothing && break
        patnext = iterate(pattern, mi)
        if patnext === nothing
            # String characters left to match, but no pattern left
            match = false
        else
            mc, mi = patnext
            if mc == '*'
                # Check if this is a **/ globstar pattern
                # Conditions: after '/' (or at start), followed by '*/'
                # Use iterate to peek ahead without string allocation
                if pathname && after_slash
                    peek1_c, peek1_s = @something iterate(pattern, mi) @goto no_globstar
                    if peek1_c == '*'
                        peek2_c, peek2_s = @something iterate(pattern, peek1_s) begin
                            # this is trailing_globstar - but check for dotfiles if PERIOD flag set
                            if period
                                j = skip_to_slash(s, i)
                                while j !== nothing
                                    peek3_c, j = @something iterate(s, j) break
                                    peek3_c == '.' && return false
                                    j == '/' || (j = skip_to_slash(s, j))
                                end
                            end
                            return true
                        end
                        if peek2_c == '/'
                            mi = peek2_s  # Skip past **/
                            # This is **/ globstar pattern - use directory-level backtracking
                            globstarmatch = i
                            globstar_mi = mi
                            # Save current star state for restoration on globstar backtrack
                            globstar_star = star
                            globstar_starmatch = starmatch
                            continue
                        end
                    end
                end
                @label no_globstar
                # Not a globstar pattern - treat as regular *
                # Even if it's **, each * will be processed separately
                starmatch = i # backup the current search index
                star = mi
                c, _ = matchnext # peek at the next character, but don't match it yet
                if period & (c == '.')
                    return false # * does not match leading .
                end
                after_slash = false
                match = true
            else
                c, i = matchnext
                if mc == '['
                    mi, valid, match = _match(pattern, mi, c, caseless, extended)
                    if pathname & valid & match & (c == '/')
                        match = false
                    end
                    if period & valid & match & (c == '.')
                        match = false
                    end
                elseif mc == '?'
                    if pathname & (c == '/')
                        return false # ? does not match /
                    end
                    if period & (c == '.')
                        return false # ? does not match leading .
                    end
                    match = true
                else
                    if (!noescape) & (mc == '\\') # escape the next character after backslash, unless it is the last character
                        patnext = iterate(pattern, mi)
                        if patnext !== nothing
                            mc, mi = patnext
                        end
                    end
                    match = ((c == mc) || (caseless && uppercase(c)==uppercase(mc)))
                end
                # Update after_slash for next iteration (track if pattern char was '/')
                after_slash = (mc == '/')
                if match && after_slash && pathname
                    # in pathname mode, once encountering a / explicitly,
                    # backtracking to starmatch will only be useful if we haven't matched anything after it
                    star = 0
                end
            end
        end
        if !match # try to backtrack
            # Try * backtracking first
            if star != 0
                c, i = something(iterate(s, starmatch))
                if !(pathname & (c == '/'))
                    mi = star
                    starmatch = i
                    continue
                end
            end
            # Then try **/ backtracking
            if globstarmatch > 0
                mi = globstar_mi
                star = globstar_star
                starmatch = globstar_starmatch
                period = periodfl
                after_slash = true
                if period
                    c, _ = @something iterate(s, globstarmatch) break
                    if c == '.'
                        return false
                    end
                end
                nextslash = skip_to_slash(s, globstarmatch)
                nextslash === nothing && break
                globstarmatch = nextslash
                i = nextslash
                continue
            end
            return false
        end
        period = (periodfl & pathname & (c == '/'))
    end
    while true # allow trailing *'s, **'s, and (if preceded by /) **/'s
        patnext = iterate(pattern, mi)
        patnext === nothing && break
        mc, mi = patnext
        mc == '*' || return false # pattern characters left to match, but no string left
        if after_slash
            patnext = iterate(pattern, mi)
            patnext === nothing && break
            mc, mi = patnext
            mc == '*' || return false # pattern characters left to match, but no string left
            patnext = iterate(pattern, mi)
            patnext === nothing && break
            mc, mi = patnext
            mc == '*' || mc == '/' || return false # pattern characters left to match, but no string left
        end
    end
    return true
end

@deprecate ismatch(fn::FilenameMatch, s::AbstractString) occursin(fn, s)

filter!(fn::FilenameMatch, v) = filter!(x -> occursin(fn, x), v)
filter(fn::FilenameMatch, v)  = filter(x -> occursin(fn, x), v)
filter!(fn::FilenameMatch, d::Dict) = filter!(((k, _),) -> occursin(fn, k), d)
filter(fn::FilenameMatch, d::Dict) = filter!(fn, copy(d))

function _match_bracket(pat::AbstractString, mc::Char, i, cl::Char, cu::Char) # returns (mc, i, valid, match)
    next = iterate(pat, i)
    if next === nothing
        return (mc, i, false, false)
    end
    mc2, j = next
    if (mc2 != ':') & (mc2 != '.') & (mc2 != '=')
        return (mc, i, false, true)
    end
    mc3 = mc4 = '\0'
    k0 = k1 = k2 = k3 = j
    next = iterate(pat, k3)
    while mc3 != mc2 && mc4 != ']'
        if next === nothing
            return (mc, i, false, false)
        end
        mc3 = mc4
        k0 = k1
        k1 = k2
        k2 = k3
        next = iterate(pat, k3)
        if next === nothing
            return (mc, i, false, false)
        end
        mc4, k3 = next
    end
    if mc2 == ':'
        phrase = SubString(pat, j, k0)
        match = (
            if phrase == "alnum"
                isletter(cl) || isnumeric(cl)
            elseif phrase == "alpha"
                isletter(cl)
            elseif phrase == "blank"
                (cl == ' ' || cl == '\t')
            elseif phrase == "cntrl"
                iscntrl(cl)
            elseif phrase == "digit"
                isdigit(cl)
            elseif phrase == "graph"
                isprint(cl) && !isspace(cl)
            elseif phrase == "lower"
                islowercase(cl) | islowercase(cu)
            elseif phrase == "print"
                isprint(cl)
            elseif phrase == "punct"
                ispunct(cl)
            elseif phrase == "space"
                isspace(cl)
            elseif phrase == "upper"
                isuppercase(cl) | isuppercase(cu)
            elseif phrase == "xdigit"
                isxdigit(cl)
            else
                error(string("invalid character expression [:",phrase,":]"))
            end)
        return (mc, k3, true, match)
    elseif mc2 == '.'
        if j != k0
            error(string("only single characters are currently supported as collating symbols, got [.", SubString(pat, j, k0), ".]"))
            #match = (pat[j:k0] == s[ci:ci+(k0-j)])
            #return (mc, k3, true, match)
        end
        mc, j = something(iterate(pat, j))
        return (mc, k3, false, true)
    else #if mc2 == '='
        if j != k0
            error(string("only single characters are currently supported as character equivalents, got [=", SubString(pat, j, k0), "=]"))
        end
        mc, j = something(iterate(pat, j))
        match = (cl==mc) | (cu==mc)
        return (mc, k3, true, match)
    end
end

function _match(pat::AbstractString, i0, c::Char, caseless::Bool, extended::Bool) # returns (i, valid, match)
    if caseless
        cl = lowercase(c)
        cu = uppercase(c)
    else
        cl = cu = c
    end
    i = i0
    next = iterate(pat, i)
    if next === nothing
        return (i0, false, c=='[')
    end
    mc, j = next
    negate = false
    if mc == '!'
        negate = true
        i = j
    end
    match = false
    notfirst = false
    while true
        next = iterate(pat, i)
        next === nothing && break
        mc, i = next
        if (mc == ']') & notfirst
            return (i, true, match ⊻ negate)
        end
        notfirst = true
        if (mc == '[')
            mc, i, valid, match2 = _match_bracket(pat, mc, i, cl, cu)
            if valid
                match |= match2
                continue
            elseif !match2
                return (i0, false, c=='[')
            end
        elseif extended & (mc == '\\')
            next = iterate(pat, i)
            if next === nothing
                return (i0, false, c=='[')
            end
            mc, i = next
        end
        next = iterate(pat, i)
        if next === nothing
            return (i0, false, c=='[')
        end
        mc2, j = next
        if mc2 == '-'
            next = iterate(pat, j)
            if next === nothing
                return (i0, false, c=='[')
            end
            mc2, j = next
            if mc2 == ']'
                match |= ((cl == mc) | (cu == mc) | (c == '-'))
                return (j, true, match ⊻ negate)
            end
            if mc2 == '['
                mc2, j, valid, match2 = _match_bracket(pat, mc2, j, cl, cu)
                if valid
                    error("[: and [= are not valid range endpoints")
                elseif !match2
                    return (i0, false, c=='[')
                end
            elseif extended & (mc2 == '\\')
                next = iterate(pat, j)
                if next === nothing
                    return (i0, false, c=='[')
                end
                mc2, j = next
            end
            match |= (mc <= cl <= mc2)
            match |= (mc <= cu <= mc2)
            i = j
        else
            match |= ((cl == mc) | (cu == mc))
        end
    end
    return (i0, false, c=='[')
end

"""
    glob"pattern"

Returns a `Glob.GlobMatch` object, which can be used with `glob()` or `readdir()`.
"""
(macro glob_str end, macro glob_mstr end, GlobMatch)

macro glob_str(pattern) GlobMatch(pattern) end
macro glob_mstr(pattern) GlobMatch(pattern) end

struct GlobMatch
    pattern::Vector{Any}
    GlobMatch(pattern) = isempty(pattern) ? error("GlobMatch pattern cannot be an empty vector") : new(pattern)
end
GlobMatch(gm::GlobMatch) = gm
function GlobMatch(pattern::AbstractString)
    if isempty(pattern) || first(pattern) == '/'
        error("Glob pattern cannot be empty or start with a / character")
    end
    pat = split(pattern, '/')
    glob = Vector{Any}(undef, length(pat))
    extended = false
    for i in eachindex(pat)
        p = pat[i]
        # Check for ** pattern
        if p == "**"
            glob[i] = GlobStar()
            continue
        end
        next = iterate(p)
        ispattern = false
        while next !== nothing
            c, j = next
            next = iterate(p, j)
            if extended & (c == '\\')
                if next === nothing
                    break
                end
                next = iterate(p, j)
            elseif (c == '*') | (c == '?') |
                    (c == '[' && _match(p, j, '\0', false, extended)[2])
                ispattern = true
                break
            end
        end
        if ispattern
            glob[i] = FilenameMatch(p, PERIOD|PATHNAME)
        else
            glob[i] = p
        end
    end
    return GlobMatch(glob)
end

function show(io::IO, gm::GlobMatch)
    for pat in gm.pattern
        if !isa(pat, AbstractString) && !isa(pat, FilenameMatch) && !isa(pat, GlobStar)
            print(io, "Glob.GlobMatch(")
            show(io, gm.pattern)
            print(io, ')')
            return
        end
    end
    print(io, "glob\"")
    notfirst = false
    for pat in gm.pattern
        notfirst && print(io, '/')
        notfirst = true
        if isa(pat, FilenameMatch)
            print(io, pat.pattern)
        elseif isa(pat, GlobStar)
            print(io, "**")
        else
            print(io, pat)
        end
    end
    print(io, '"')
end

"""
    GlobStar()

A singleton pattern that matches any file/directory name except `.*`,
and can also match zero or more subsequent entries when used with `occursin(::GlobMatch, ::AbstractVector)`.

When matching against arrays, `GlobStar()` acts as a multi-level wildcard, similar to
`**/` in pathname glob patterns without the `PERIOD` flag set.

!!! note
    A trailing `/` in a glob pattern (e.g., `glob"**/"`) parses to `[GlobStar(), ""]`.
    This differs from `splitpath` (which omits trailing empty strings) but agrees with
    `joinpath(splitdir("**/")...)` behavior. When matching arrays, include an empty
    string at the end to match patterns with trailing slashes.

# Example
```julia
gm = GlobMatch(["src", GlobStar(), fn"*.jl"])
occursin(gm, ["src", "foo.jl"])           # true - GlobStar matches zero elements
occursin(gm, ["src", "a", "foo.jl"])      # true - GlobStar matches "a"
occursin(gm, ["src", "a", "b", "foo.jl"]) # true - GlobStar matches "a", "b"
occursin(gm, ["src", ".a", "foo.jl"])     # false - GlobStar does not match ".a"
```
"""
struct GlobStar end
occursin(::GlobStar, s::AbstractString) = !startswith(s, '.')

"""
    occursin(gm::GlobMatch, arr::AbstractVector)

Test whether a `GlobMatch` pattern matches an array of path components (strings).

Each element of the pattern is matched against the corresponding element of the array:
- `AbstractString` patterns require exact equality.
- `FilenameMatch` patterns use `occursin` for matching.
- `GlobStar()` matches any single element (except a leading `.`),
   and can also consume zero or more additional elements.

Returns `true` if the entire pattern matches the entire array.

# Examples
```julia
gm = glob"src/*/test.jl"
occursin(gm, ["src", "foo", "test.jl"])  # true
occursin(gm, ["src", "bar", "test.jl"])  # true
occursin(gm, ["src", "test.jl"])         # false - wrong length

gm = GlobMatch(["src", GlobStar(), fn"*.jl"])
occursin(gm, ["src", "foo.jl"])           # true
occursin(gm, ["src", "a", "b", "foo.jl"]) # true
```
"""
occursin(gm::GlobMatch, arr::AbstractVector) = occursin_sub(gm, firstindex(gm.pattern), arr)
function occursin_sub(gm::GlobMatch, pi::Int, arr::AbstractVector)
    pattern = gm.pattern
    ai = firstindex(arr)
    # Track the most recent GlobStar ** for backtracking
    globstar_pi = 0 # Pattern index after the GlobStar
    globstar_ai = 0 # Array index to resume from on backtrack
    while true
        if pi > lastindex(pattern)
            # Pattern exhausted; check if array is also exhausted
            if ai > lastindex(arr)
                return true
            end
            # Array has remaining elements - try backtracking
        else
            pat = pattern[pi]
            pi += 1
            if pat isa GlobStar
                # Save restart point for backtracking (only most recent matters)
                globstar_pi = pi
                globstar_ai = ai  # Start by matching zero elements
                if pi > lastindex(pattern)
                    # Quick exit for patterns ending in ** - but check no dotfiles remain
                    for j in ai:lastindex(arr)
                        startswith(arr[j], '.') && return false
                    end
                    return true
                end
                continue
            end
            # Regular pattern: must have a corresponding array element
            if ai <= lastindex(arr)
                arr_ai = arr[ai]
                ai += 1
                matched = if pat isa FilenameMatch
                        occursin(pat, arr_ai)
                    elseif pat isa AbstractString
                        pat == arr_ai
                    else
                        # For other types that support occursin (e.g., Regex)
                        occursin(pat, arr_ai)
                    end
                if matched
                    continue
                end
            end
        end
        # Try consuming one more element with the most recent **
        if globstar_pi > 0 && globstar_ai <= lastindex(arr) && !startswith(arr[globstar_ai], '.')
            globstar_ai += 1
            ai = globstar_ai
            pi = globstar_pi
            continue
        end
        return false
    end
end

"""
    readdir(pattern::GlobMatch, [directory::AbstractString]; join::Bool=true, sort::Bool=true)

Alias for [`glob()`](@ref).
"""
readdir(pattern::GlobMatch, prefix=""; join::Bool=true, sort::Bool=true) = glob(pattern, prefix; join=join, sort=sort)

"""
    glob(pattern, [directory::AbstractString]; join::Bool=true, sort::Bool=true)

Returns a list of all files matching `pattern` in `directory`.

* If directory is not specified, it defaults to the current working directory.
* If `join` is `true` (default), the results are joined with the directory path. If `false`, only the matched paths relative to the directory are returned.
* If `sort` is `true` (default), the results are sorted lexicographically.
* Pattern can be any of:
    1. A `Glob.GlobMatch` object:

            glob"a/?/c"

    2. A string, which will be converted into a GlobMatch expression:

            "a/?/c" # equivalent to 1, above

    3. A vector of strings and/or objects which implement `occursin`, including `Regex` and `Glob.FilenameMatch` objects

            ["a", r".", fn"c"] # again, equivalent to 1, above

        * Each element of the vector will be used to match another level in the file hierarchy
        * no conversion of strings to `Glob.FilenameMatch` objects or directory splitting on `/` will occur.

A trailing `/` (or equivalently, a trailing empty string in the vector) will cause glob to only match directories.

Attempting to use a pattern with a leading `/` or the empty string is an error; use the `directory` argument to specify the absolute path to the directory in such a case.
"""
function glob(pattern, prefix=""; join::Bool=true, sort::Bool=true)
    if prefix isa AbstractString && !(prefix isa String)
        prefix = String(prefix)::String
    end
    gm = GlobMatch(pattern)
    pats = gm.pattern
    matches = [""]  # relative paths (without prefix)
    for i in eachindex(pats)
        pat = pats[i]
        if pat isa GlobStar
            # GlobStar: enumerate all paths recursively and filter by remaining pattern
            matches = _globstar!(prefix, matches, i, gm, sort)
            break
        else
            matches = _glob!(prefix, matches, pat, sort)
        end
    end
    if join && !(prefix isa AbstractString && isempty(prefix))
        newmatches = prefix isa AbstractString ? matches : Vector{typeof(prefix)}(undef, length(matches))
        for j in eachindex(matches)
            m = matches[j]
            newmatches[j] = isempty(m) ? prefix : joinpath(prefix, m)
        end
        matches = newmatches
    end
    return matches
end

function _globstar!(prefix::AbstractString, matches, i::Int, gm::GlobMatch, sort::Bool)
    results = empty(matches)
    workqueue = Vector{String}[]
    components = String[]
    for relpath in matches
        # Build the actual filesystem path
        fspath = isempty(relpath) ? prefix : joinpath(prefix, relpath)

        # Seed workqueue with directory contents
        if isempty(fspath)
            push!(workqueue, _readdir(; sort=sort))
        else
            if isdir(fspath)
                push!(workqueue, _readdir(fspath; sort=sort))
                push!(components, "")
            end

            # GlobStar can match zero elements - check relpath itself
            if occursin_sub(gm, i, components)
                push!(results, relpath)
            end

            isempty(components) || pop!(components)
        end

        while !isempty(workqueue)
            paths = pop!(workqueue)
            if isempty(paths)
                isempty(components) || pop!(components)
            else
                pathcomp = popfirst!(paths)
                push!(workqueue, paths)
                push!(components, pathcomp)
                # Build relative path (for results) and filesystem path (for isdir/readdir)
                newrelpath = joinpath(relpath, components...)
                fspath = joinpath(prefix, newrelpath)

                # If directory, add contents to workqueue for further exploration
                if isdir(fspath)
                    push!(workqueue, _readdir(fspath; sort=sort))
                    push!(components, "")
                end

                # Check if this path matches remaining pattern
                if occursin_sub(gm, i, components)
                    push!(results, newrelpath)
                end

                pop!(components)
            end
        end
    end
    return results
end

@static if VERSION >= v"1.4"
    _readdir(; sort::Bool) = Base.readdir(; sort=sort)
    _readdir(dir; sort::Bool) = Base.readdir(dir; sort=sort)
else
    _readdir(; sort::Bool) = Base.readdir()
    _readdir(dir; sort::Bool) = Base.readdir(dir)
end

function _glob!(prefix::AbstractString, matches, pat::AbstractString, sort::Bool)
    i = j = k = firstindex(matches)
    last = lastindex(matches)
    while i <= last
        relpath = joinpath(matches[i], pat)
        fspath = joinpath(prefix, relpath)
        i += 1
        if ispath(fspath)
            matches[j] = relpath
            j += 1
        end
    end
    resize!(matches, j - k)
    return matches
end

function _glob!(prefix::AbstractString, matches, pat, sort::Bool)
    m2 = empty(matches)
    for m in matches
        fspath = isempty(m) ? prefix : joinpath(prefix, m)
        if isempty(fspath)
            for d in _readdir(; sort=sort)
                if occursin(pat, d)
                    push!(m2, d)
                end
            end
        elseif isdir(fspath)
            for d in _readdir(fspath; sort=sort)
                if occursin(pat, d)
                    push!(m2, joinpath(m, d))
                end
            end
        end
    end
    return m2
end

end # module
