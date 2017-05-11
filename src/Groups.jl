module Groups

using Nemo
import Nemo: Group, parent

import Base: length, ==, hash, show, convert
import Base: inv, reduce, *, ^
import Base: findfirst, findnext
import Base: deepcopy_internal


export GSymbol, GWord

doc"""
    ::GSymbol
> Abstract type which all group symbols of FPGroups should subtype. Each
> concrete subtype should implement fields:
> * `str` which is the string representation/identification of a symbol
> * `pow` which is the (multiplicative) exponent of a symbol.

"""
abstract GSymbol

doc"""
    W::GWord{T<:GSymbol} <:GroupElem
> Basic representation of element of a finitely presented group. `W.symbols`
> fieldname contains particular group symbols which multiplied constitute a
> group element, i.e. a word in generators.
> As reduction (inside group) of such word may be time consuming we provide
> `savedhash` and `modified` fields as well:
> hash (used e.g. in the `unique` function) is calculated by reducing the word,
> setting `modified` flag to `false` and computing the hash which is stored in
> `savedhash` field.
> whenever word `W` is changed `W.modified` is set to `false`;
> Future comparisons don't perform reduction (and use `savedhash`) as long as
> `modified` flag remains `false`.

"""

type GWord{T<:GSymbol} <: GroupElem
    symbols::Vector{T}
    savedhash::UInt
    modified::Bool
    parent::Group

    function GWord(symbols::Vector{T})
        return new(symbols, hash(symbols), true)
    end
end



parent{T<:GSymbol}(w::GWord{T}) = w.parent

GWord{T<:GSymbol}(s::T) = GWord{T}(T[s])
convert{T<:GSymbol}(::Type{GWord{T}}, s::T) = GWord{T}(T[s])


function hash(W::GWord, h::UInt)
    W.modified && reduce!(W)
    return W.savedhash $ h
end

function deepcopy_internal{T<:GSymbol}(W::GWord{T}, dict::ObjectIdDict)
    G = parent(W)
    return G(GWord{T}(deepcopy(W.symbols)))
end

length(W::GWord) = sum([length(s) for s in W.symbols])

function free_reduce!(W::GWord)
    reduced = true
    for i in 1:length(W.symbols) - 1
        if W.symbols[i].gen == W.symbols[i+1].gen
            reduced = false
            p1 = W.symbols[i].pow
            p2 = W.symbols[i+1].pow
            W.symbols[i+1] = change_pow(W.symbols[i], p1 + p2)
            W.symbols[i] = change_pow(W.symbols[i], 0)
        end
    end
    deleteat!(W.symbols, find(x -> x.pow == 0, W.symbols))
    return reduced
end

function reduce!(W::GWord)
    if length(W) < 2
        deleteat!(W.symbols, find(x -> x.pow == 0, W.symbols))
    else
        reduced = false
        while !reduced
            reduced = free_reduce!(W)
        end
    end

    W.modified = false
    W.savedhash = hash(W.symbols, hash(typeof(W)))
    return W
end

doc"""
    reduce(W::GWord)
> performs reduction/simplification of a group element (word in generators).
> The default reduction is the free group reduction, i.e. consists of
> multiplying adjacent symbols with the same `str` identifier and deleting the
> identity elements from `W.symbols`.
> More specific procedures should be dispatched on `GWord`s type parameter.

"""
reduce(W::GWord) = reduce!(deepcopy(W))



function show(io::IO, W::GWord)
    if length(W) == 0
        print(io, "(id)")
    else
        join(io, [string(s) for s in W.symbols], "*")
    end
end

function (==)(W::GWord, Z::GWord)
    parent(W) == parent(Z) || return false
    W.modified && reduce!(W) # reduce clears the flag and calculates savedhash
    Z.modified && reduce!(Z)
    return W.savedhash == Z.savedhash && W.symbols == Z.symbols
end

function r_multiply!(W::GWord, x; reduced::Bool=true)
    if length(x) > 0
        push!(W.symbols, x...)
    end
    if reduced
        reduce!(W)
    end
    return W
end

function l_multiply!(W::GWord, x; reduced::Bool=true)
    if length(x) > 0
        unshift!(W.symbols, reverse(x)...)
    end
    if reduced
        reduce!(W)
    end
    return W
end

r_multiply(W::GWord, x; reduced::Bool=true) =
    r_multiply!(deepcopy(W),x, reduced=reduced)
l_multiply(W::GWord, x; reduced::Bool=true) =
    l_multiply!(deepcopy(W),x, reduced=reduced)

(*)(W::GWord, Z::GWord) = r_multiply(W, Z.symbols)
(*)(W::GWord, s::GSymbol) = r_multiply(W, [s])
(*)(s::GSymbol, W::GWord) = l_multiply(W, [s])

function power_by_squaring(W::GWord, p::Integer)
    if p < 0
        return power_by_squaring(inv(W), -p)
    elseif p == 0
        return parent(W)()
    elseif p == 1
        return W
    elseif p == 2
        return W*W
    end
    W = deepcopy(W)
    t = trailing_zeros(p) + 1
    p >>= t
    while (t -= 1) > 0
        r_multiply!(W, W.symbols)
    end
    Z = deepcopy(W)
    while p > 0
        t = trailing_zeros(p) + 1
        p >>= t
        while (t -= 1) >= 0
            r_multiply!(W, W.symbols)
        end
        r_multiply!(Z, W.symbols)
    end
    return Z
end

(^)(x::GWord, n::Integer) = power_by_squaring(x,n)

###############################################################################

function inv{T}(W::GWord{T})
    if length(W) == 0
        return W
    else
        G = parent(W)
        w = GWord{T}(reverse([inv(s) for s in W.symbols]))
        w.modified = true
        return G(w)
    end
end

is_subsymbol(s::GSymbol, t::GSymbol) =
    s.gen == t.gen && (0 ≤ s.pow ≤ t.pow || 0 ≥ s.pow ≥ t.pow)

function findfirst(W::GWord, Z::GWord)
    n = length(Z.symbols)

    @assert n > 1
    for (idx,a) in enumerate(W.symbols)
        if idx + n - 1 > length(W.symbols)
            break
        end
        first = is_subsymbol(Z.symbols[1],a)
        if first
            middle = W.symbols[idx+1:idx+n-2] == Z.symbols[2:end-1]
            last = is_subsymbol(Z.symbols[end], W.symbols[idx+n-1])
            if middle && last
                return idx
            end
        end
    end
    return 0
end

function findnext(W::GWord, Z::GWord, i::Integer)
    t = findfirst(GWord{eltype(W.symbols)}(W.symbols[i:end]), Z)
    if t > 0
        return t+i-1
    else
        return 0
    end
end

function replace!(W::GWord, index, toreplace::GWord, replacement::GWord; asserts=true)
    n = length(toreplace.symbols)
    if asserts
        @assert is_subsymbol(toreplace.symbols[1], W.symbols[index])
        @assert W.symbols[index+1:index+n-2] == toreplace.symbols[2:end-1]
        @assert is_subsymbol(toreplace.symbols[end], W.symbols[index+n-1])
    end

    first = W.symbols[index]*inv(toreplace.symbols[1])
    last = W.symbols[index+n-1]*inv(toreplace.symbols[end])
    replacement = first*replacement*last
    splice!(W.symbols, index:index+n-1, replacement.symbols)
    return reduce!(W)
end

function replace(W::GWord, index, toreplace::GWord, replacement::GWord)
    replace!(deepcopy(W), index, toreplace, replacement)
end

function replace_all!{T}(W::GWord{T}, subst_dict::Dict{GWord{T}, GWord{T}})
    for toreplace in reverse!(sort!(collect(keys(subst_dict)),by=length))
        replacement = subst_dict[toreplace]
        i = findfirst(W, toreplace)
        while i ≠ 0
            replace!(W,i,toreplace, replacement)
            i = findnext(W, toreplace, i)
        end
    end
    return W
end

replace_all(W::GWord, subst_dict::Dict{GWord, GWord}) = replace_all!(deepcopy(W), subst_dict)

include("free_groups.jl")
include("automorphism_groups.jl")

end # of module Groups
