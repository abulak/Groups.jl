include("transvections.jl")
include("gersten_relations.jl")

function SpecialAutomorphismGroup(F::FreeGroup; ordering = KnuthBendix.LenLex, kwargs...)

    n = length(alphabet(F)) ÷ 2
    A, rels = gersten_relations(n, commutative = false)
    S = KnuthBendix.letters(A)[1:2(n^2-n)]

    maxrules = 1000*n

    rws = KnuthBendix.RewritingSystem(rels, ordering(A))
    @time KnuthBendix.knuthbendix!(rws; maxrules=maxrules, kwargs...)
    return AutomorphismGroup(F, S, rws, ntuple(i -> gens(F, i), n))
end

KnuthBendix.alphabet(G::AutomorphismGroup{<:FreeGroup}) = alphabet(rewriting(G))

function relations(G::AutomorphismGroup{<:FreeGroup})
    n = length(alphabet(object(G))) ÷ 2
    return last(gersten_relations(n, commutative = false))
end
