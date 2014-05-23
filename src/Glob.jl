module Glob

import Base: ismatch, match, readdir, show

export glob, @fn_str, @fn_mstr, @glob_str, @glob_mstr

const CASELESS = 1 << 0 # Do case-insensitive matching
const PERIOD   = 1 << 1 # A leading period (.) character must be exactly matched by a period (.) character
const NOESCAPE = 1 << 2 # Do not treat backslash (\) as a special character
const PATHNAME = 1 << 3 # Slash (/) character must be exactly matched by a slash (/) character

immutable FilenameMatch{S<:String}
    pattern::S
    options::Uint32
    FilenameMatch(pattern, options) = new(pattern, options)
end
function FilenameMatch{S<:String}(pattern::S, options::Integer=0)
    FilenameMatch{S}(pattern, options)
end
function FilenameMatch(pattern::String, flags::String)
    options = 0
    for f in flags
        options |= f=='i' ? CASELESS  :
                   f=='p' ? PERIOD    :
                   f=='e' ? NOESCAPE  :
                   f=='d' ? PATHNAME  :
                   error("unknown Filename Matcher flag: $f")
    end
    FilenameMatch(pattern, options)
end
macro fn_str(pattern, flags...) FilenameMatch(pattern, flags...) end
macro fn_mstr(pattern, flags...) FilenameMatch(pattern, flags...) end

function show(io::IO, fn::FilenameMatch)
    print(io, "fn\"", fn.pattern, '"')
    (fn.options&CASELESS)!=0 && print(io, 'i')
    (fn.options&PERIOD  )!=0 && print(io, 'p')
    (fn.options&NOESCAPE)!=0 && print(io, 'e')
    (fn.options&PATHNAME)!=0 && print(io, 'd')
end

function ismatch(fn::FilenameMatch, s::String)
    pattern = fn.pattern
    periodfl = (fn.options&PERIOD  )!=0
    noescape = (fn.options&NOESCAPE)!=0
    caseless = (fn.options&CASELESS)!=0
    pathname = (fn.options&PATHNAME)!=0
    mi = start(pattern) # current index into pattern
    i = start(s) # current index into s
    starmatch = i
    star = 0
    period = periodfl
    while !done(s, i)
        if done(pattern, mi)
            match = false # string characters left to match, but no pattern left
        else
            mc, mi = next(pattern, mi)
            if mc == '*'
                starmatch = i # backup the current search index
                star = mi
                c = next(s, i)[1] # peek-ahead
                if period & (c == '.')
                    return false # * does not match leading .
                end
                match = true
            else
                c, i = next(s, i)
                if mc == '['
                    mi, valid, match = _match(pattern, mi, c, caseless)
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
                    if (!noescape) & (mc == '\\') & (!done(pattern, mi))
                        mc, mi = next(pattern, mi)
                    end
                    match = ((c == mc) || (caseless && uppercase(c)==uppercase(mc)))
                end
            end
        end
        if !match # try to backtrack and add another character to the last *
            star == 0 && return false
            c, i = next(s, starmatch)
            if pathname & (c == '/')
                return false # * does not match /
            end
            mi = star
            starmatch = i
        end
        period = (periodfl & pathname & (c == '/'))
    end
    while !done(pattern, mi) # allow trailing *'s
        mc, mi = next(pattern, mi)
        if mc != '*'
            return false # pattern characters left to match, but no string left
        end
    end
    return true
end
filter!(fn::FilenameMatch, v) = filter!(x->ismatch(fn,x), v)
filter(fn::FilenameMatch, v)  = filter(x->ismatch(fn,x), v)
filter!(fn::FilenameMatch, d::Dict) = filter!((k,v)->ismatch(fn,k),d)
filter(fn::FilenameMatch, d::Dict) = filter!(fn,copy(d))

function _match(pat::String, i0, c::Char, caseless::Bool) # returns (i, valid, match)
    if caseless
        cl = lowercase(c)
        cu = uppercase(c)
    else
        cl = cu = c
    end
    i = i0
    if done(pat, i)
        return (i0, false, c=='[')
    end
    mc, j = next(pat, i)
    negate = false
    if mc == '!'
        negate = true
        i = j
        if done(pat, i)
            return (i0, false, c=='[')
        end
        mc, j = next(pat, i)
    end
    match = false
    notfirst = false
    while !done(pat,i)
        mc, i = next(pat, i)
        if (mc == ']') & notfirst
            return (i, true, match$negate)
        end
        notfirst = true
        if done(pat, i)
            return (i0, false, c=='[')
        end
        mc2, j = next(pat, i)
        if (mc == '[') & ((mc2 == '.') | (mc2 == ':') | (mc2 == '='))
            error("[: [. and [= are not currently supported")
        else
            if mc == '\\'
                mc, i = mc2, j
                if done(pat, i)
                    return (i0, false, c=='[')
                end
                mc2, j = next(pat, i)
            end
            if mc2 == '-'
                if done(pat, j)
                    return (i0, false, c=='[')
                end
                mc2, j = next(pat, j)
                if mc2 == ']'
                    match |= ((cl == mc) | (cu == mc) | (c == '-'))
                    return (j, true, match$negate)
                end
                if mc2 == '['
                    if done(pat, j)
                        return (i0, false, c=='[')
                    end
                    mc3, k = next(pat, j)
                    if mc3 == '.'
                        error("[. is not currently supported")
                    end
                    if (mc3 == ':') | (mc3 == '=')
                        error("[: and [= are not valid range endpoints")
                    end
                elseif mc2 == '\\'
                    if done(pat, j)
                        return (i0, false, c=='[')
                    end
                    mc2, j = next(pat, j)
                end
                match |= (mc <= cl <= mc2)
                match |= (mc <= cu <= mc2)
                i = j
            else
                match |= ((cl == mc) | (cu == mc))
            end
        end
    end
    return (i0, false, c=='[')
end

macro glob_str(pattern) GlobMatch(pattern) end
macro glob_mstr(pattern) GlobMatch(pattern) end

immutable GlobMatch
    pattern::Vector
    GlobMatch(pattern) = isempty(pattern) ? error("GlobMatch pattern cannot be an empty vector") : new(pattern)
end
GlobMatch(gm::GlobMatch) = gm
function GlobMatch(pattern::String)
    pat = split(pattern, '/')
    S = eltype(pat)
    if !isleaftype(S)
        S = Any
    else
        S = Union(S, FilenameMatch{S})
    end
    glob = Array(S, length(pat))
    for i = 1:length(pat)
        p = pat[i]
        j = start(p)
        ispattern = false
        while !done(p, j)
            c, j = next(p, j)
            if c == '\\'
                if done(p, j)
                    break
                end
                c, j = next(p, j)
            elseif (c == '*') | (c == '?') |
                    (c == '[' && _match(p, j, '\0', false)[2])
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
        if !isa(pat, String) && !isa(pat, FilenameMatch)
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
        else
            print(io, pat)
        end
    end
    print(io, '"')
end

readdir(pattern::GlobMatch, prefix::String="") = glob(pattern, prefix)

function glob(pattern, prefix::String="")
    matches = ByteString[prefix]
    for pat in GlobMatch(pattern).pattern
        matches = _glob!(matches, pat)
    end
    return matches
end

function _glob!(matches, pat::String)
    i = 1
    last = length(matches)
    while i <= last
        path = joinpath(matches[i], pat)
        if ispath(path)
            matches[i] = path
            i += 1
        else
            matches[i] = matches[last]
            last -= 1
        end
    end
    resize!(matches, last)
    matches
end

function _glob!(matches, pat)
    m2 = ByteString[]
    for m in matches
        if isempty(m)
            for d in readdir()
                if ismatch(pat, d)
                    push!(m2, d)
                end
            end
        elseif isdir(m)
            for d in readdir(m)
                if ismatch(pat, d)
                    push!(m2, joinpath(m, d))
                end
            end
        end
    end
    m2
end

end # module
