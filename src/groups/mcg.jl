struct SurfaceGroup{T, S, R} <: AbstractFPGroup
    genus::Int
    boundaries::Int
    gens::Vector{T}
    relations::Vector{<:Pair{S,S}}
    rws::R
end

include("symplectic_twists.jl")

genus(S::SurfaceGroup) = S.genus

function Base.show(io::IO, S::SurfaceGroup)
    print(io, "π₁ of the orientable surface of genus $(genus(S))")
    if S.boundaries > 0
        print(io, " with $(S.boundaries) boundary components")
    end
end

function SurfaceGroup(genus::Integer, boundaries::Integer)
    @assert genus > 1

    ltrs = String[]
    for i in 1:genus
        subscript = join('₀'+d for d in reverse(digits(i)))
        append!(ltrs, ["a" * subscript, "A" * subscript, "b" * subscript, "B" * subscript])
    end
    Al = Alphabet(reverse!(ltrs))

    for i in 1:genus
        subscript = join('₀'+d for d in reverse(digits(i)))
        KnuthBendix.set_inversion!(Al, "a" * subscript, "A" * subscript)
        KnuthBendix.set_inversion!(Al, "b" * subscript, "B" * subscript)
    end

    if boundaries == 0
        word = Int[]

        for i in reverse(1:genus)
            x = 4 * i
            append!(word, [x, x-2, x-1, x-3])
        end
        comms = Word(word)
        word_rels = [ comms => one(comms) ]

        rws = KnuthBendix.RewritingSystem(word_rels, KnuthBendix.RecursivePathOrder(Al))
        KnuthBendix.knuthbendix!(rws)
    elseif boundaries == 1
        S = typeof(one(Word(Int[])))
        word_rels = Pair{S, S}[]
        rws = RewritingSystem(word_rels, KnuthBendix.LenLex(Al))
    else
        throw("Not Implemented")
    end

    F = FreeGroup(alphabet(rws))
    rels = [F(lhs)=>F(rhs) for (lhs,rhs) in word_rels]

    return SurfaceGroup(genus, boundaries, KnuthBendix.letters(Al)[2:2:end], rels, rws)
end

rewriting(S::SurfaceGroup) = S.rws
KnuthBendix.alphabet(S::SurfaceGroup) = alphabet(rewriting(S))
relations(S::SurfaceGroup) = S.relations

function symplectic_twists(π₁Σ::SurfaceGroup)
    g = genus(π₁Σ)

    saut = SpecialAutomorphismGroup(FreeGroup(2g))

    Aij  = [SymplecticMappingClass(π₁Σ, saut, :A, i, j) for i in 1:g for j in 1:g if i≠j]

    Bij  = [SymplecticMappingClass(π₁Σ, saut, :B, i, j) for i in 1:g for j in i+1:g]

    mBij = [SymplecticMappingClass(π₁Σ, saut, :B, i, j, minus=true) for i in 1:g for j in i+1:g]

    Bii  = [SymplecticMappingClass(π₁Σ, saut, :B, i, i) for i in 1:g]

    mBii = [SymplecticMappingClass(π₁Σ, saut, :B, i, i, minus=true) for i in 1:g]

    return [Aij; Bij; mBij; Bii; mBii]
end

KnuthBendix.alphabet(G::AutomorphismGroup{<:SurfaceGroup}) = rewriting(G)

function AutomorphismGroup(π₁Σ::SurfaceGroup; kwargs...)
    S = vcat(symplectic_twists(π₁Σ)...)
    A = Alphabet(S)
    return AutomorphismGroup(π₁Σ, S, A, ntuple(i->gens(π₁Σ, i), 2genus(π₁Σ)))
end
