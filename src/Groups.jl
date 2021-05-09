module Groups

using GroupsCore
using LinearAlgebra
using ThreadsX

import AbstractAlgebra
import KnuthBendix

export gens, FreeGroup, Aut, SAut

include("types.jl")

include("FreeGroup.jl")
include("FPGroups.jl")
include("AutGroup.jl")

include("symbols.jl")
include("words.jl")
include("hashing.jl")
include("freereduce.jl")
include("arithmetic.jl")
include("findreplace.jl")

module New
import Groups: AutSymbol, GSymbol, λ, ϱ, RTransvect, LTransvect
using DataStructures

include("new_types.jl")
include("new_hashing.jl")
include("normalform.jl")

include("gersten_relations.jl")
include("new_autgroups.jl")

end # module New

###############################################################################
#
#   String I/O
#

function Base.show(io::IO, W::GWord)
    if length(W) == 0
        print(io, "(id)")
    else
        join(io, (string(s) for s in syllables(W)), "*")
    end
end

function Base.show(io::IO, s::T) where {T<:GSymbol}
    if s.pow == 1
        print(io, string(s.id))
    else
        print(io, "$(s.id)^$(s.pow)")
    end
end

###############################################################################
#
#   Misc
#

GroupsCore.gens(G::AbstractFPGroup) = G.(G.gens)

"""
    wlmetric_ball(S::AbstractVector{<:GroupElem}
        [, center=one(first(S)); radius=2, op=*])
Compute metric ball as a list of elements of non-decreasing length, given the
word-length metric on the group generated by `S`. The ball is centered at `center`
(by default: the identity element). `radius` and `op` keywords specify the
radius and multiplication operation to be used.
"""
function wlmetric_ball_serial(S::AbstractVector{T}; radius = 2, op = *) where {T}
    @assert radius > 0
    old = unique!([one(first(S)), S...])
    sizes = [1, length(old)]
    for i in 2:radius
        new = collect(op(o, s) for o in @view(old[sizes[end-1]:end]) for s in S)
        append!(old, new)
        resize!(new, 0)
        old = unique!(old)
        push!(sizes, length(old))
    end
    return old, sizes[2:end]
end

function wlmetric_ball_thr(S::AbstractVector{T}; radius = 2, op = *) where {T}
    @assert radius > 0
    old = unique!([one(first(S)), S...])
    sizes = [1, length(old)]
    for r in 2:radius
        begin
            new =
                ThreadsX.collect(op(o, s) for o in @view(old[sizes[end-1]:end]) for s in S)
            ThreadsX.foreach(hash, new)
        end
        append!(old, new)
        resize!(new, 0)
        old = ThreadsX.unique(old)
        push!(sizes, length(old))
    end
    return old, sizes[2:end]
end

function wlmetric_ball_serial(S::AbstractVector{T}, center::T; radius = 2, op = *) where {T}
    E, sizes = wlmetric_ball_serial(S, radius = radius, op = op)
    isone(center) && return E, sizes
    return c .* E, sizes
end

function wlmetric_ball_thr(S::AbstractVector{T}, center::T; radius = 2, op = *) where {T}
    E, sizes = wlmetric_ball_thr(S, radius = radius, op = op)
    isone(center) && return E, sizes
    return c .* E, sizes
end

function wlmetric_ball(
    S::AbstractVector{T},
    center::T = one(first(S));
    radius = 2,
    op = *,
    threading = true,
) where {T}
    threading && return wlmetric_ball_thr(S, center, radius = radius, op = op)
    return wlmetric_ball_serial(S, center, radius = radius, op = op)
end

"""
    image(w::GWord, homomorphism; kwargs...)
Evaluate homomorphism `homomorphism` on a group word (element) `w`.
`homomorphism` needs to implement
> `hom(w; kwargs...)`,
where `hom(;kwargs...)` returns the value at the identity element.
"""
function image(w::GWord, hom; kwargs...)
    return reduce(
        *,
        (hom(s; kwargs...) for s in syllables(w)),
        init = hom(; kwargs...),
    )
end

end # of module Groups
