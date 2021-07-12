struct Transvection <: GSymbol
    id::Symbol
    ij::UInt8
    inv::Bool

    function Transvection(id::Symbol, i::Integer, j::Integer, inv = false)
        @assert id in (:ϱ, :λ)
        @boundscheck @assert 0 < i <= (typemax(UInt8) >> 4)
        @boundscheck @assert 0 < j <= (typemax(UInt8) >> 4)
        return new(id, (convert(UInt8, i) << 4) + convert(UInt8, j), inv)
    end
end

ϱ(i, j) = Transvection(:ϱ, i, j)
λ(i, j) = Transvection(:λ, i, j)

_tophalf(ij::UInt8) = (ij & 0xf0) >> 4
_bothalf(ij::UInt8) = (ij & 0x0f)

function Base.getproperty(t::Transvection, s::Symbol)
    s === :i && return _tophalf(t.ij)
    s === :j && return _bothalf(t.ij)
    return Core.getfield(t, s)
end

function Base.show(io::IO, t::Transvection)
    id = if t.id === :ϱ
        'ϱ'
    else # if t.id === :λ
        'λ'
    end
    print(io, id, subscriptify(t.i), '.', subscriptify(t.j))
    t.inv && print(io, "^-1")
end

Base.inv(t::Transvection) =
    Transvection(t.id, _tophalf(t.ij), _bothalf(t.ij), !t.inv)

Base.:(==)(t::Transvection, s::Transvection) =
    t.id === s.id && t.ij == s.ij && t.inv == s.inv
Base.hash(t::Transvection, h::UInt) = hash(t.id, hash(t.ij, hash(t.inv, h)))

Base.@propagate_inbounds function evaluate!(v::NTuple{T, N}, t::Transvection, A::Alphabet, tmp=one(first(v))) where {T, N}
    i, j = t.i, t.j
    @assert i ≤ length(v) && j ≤ length(v)

    @inbounds begin
        if t.id === :ϱ
            if !t.inv
                append!(word(v[i]), word(v[j]))
            else
                # append!(word(v[i]), inv(A, word(v[j])))
                for l in Iterators.reverse(word(v[j]))
                    push!(word(v[i]), inv(A, l))
                end
            end
        else # if t.id === :λ
            if !t.inv
                # prepend!(word(v[i]), word(v[j]))
                for l in Iterators.reverse(word(v[j]))
                    pushfirst!(word(v[i]), l)
                end
            else
                # prepend!(word(v[i]), inv(A, word(v[j])))
                for l in word(v[j])
                    pushfirst!(word(v[i]), inv(A, l))
                end
            end
        end

        _setnormalform!(v[i], false)
        _setvalidhash!(v[i], false)
    end
    normalform!(tmp, v[i])
    copyto!(v[i], tmp)

    return v
end

struct PermRightAut <: GSymbol
    perm::Vector{UInt8}

    function PermRightAut(p::AbstractVector{<:Integer})
        @assert sort(p) == 1:length(p)
        return new(p)
    end
end

function Base.show(io::IO, p::PermRightAut)
    print(io, 'σ')
    join(io, (subscriptify(Int(i)) for i in p.perm))
end

Base.inv(p::PermRightAut) = PermRightAut(invperm(p.perm))

Base.:(==)(p::PermRightAut, q::PermRightAut) = p.perm == q.perm
Base.hash(p::PermRightAut, h::UInt) = hash(p.perm, hash(PermRightAut, h))

function evaluate!(v::NTuple{T, N}, p::PermRightAut, ::Alphabet, tmp=one(first(v))) where {T, N}
    return v[p.perm]
end
