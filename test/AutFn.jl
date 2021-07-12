@testset "Automorphisms" begin

    @testset "Transvections" begin

        @test Groups.Transvection(:ϱ, 1, 2) isa Groups.GSymbol
        @test Groups.Transvection(:ϱ, 1, 2) isa Groups.Transvection
        @test Groups.Transvection(:λ, 1, 2) isa Groups.GSymbol
        @test Groups.Transvection(:λ, 1, 2) isa Groups.Transvection
        t = Groups.Transvection(:ϱ, 1, 2)
        @test inv(t) isa Groups.GSymbol
        @test inv(t) isa Groups.Transvection

        @test t != inv(t)

        s = Groups.Transvection(:ϱ, 1, 2)
        @test t == s
        @test hash(t) == hash(s)

        s_ = Groups.Transvection(:ϱ, 1, 3)
        @test s_ != s
        @test hash(s_) != hash(s)

        @test Groups.gersten_alphabet(3) isa Alphabet
        A = Groups.gersten_alphabet(3)
        @test length(A) == 12

        @test sprint(show, Groups.ϱ(1, 2)) == "ϱ₁.₂"
        @test sprint(show, Groups.λ(3, 2)) == "λ₃.₂"
    end

    A4 = Alphabet(
    [:a,:A,:b,:B,:c,:C,:d,:D],
    [ 2, 1, 4, 3, 6, 5, 8, 7]
    )

    A5 = Alphabet(
    [:a,:A,:b,:B,:c,:C,:d,:D,:e,:E],
    [ 2, 1, 4, 3, 6, 5, 8, 7,10, 9]
    )

    F4 = FreeGroup([:a, :b, :c, :d], A4)
    a,b,c,d = gens(F4)
    D = ntuple(i->gens(F4, i), 4)

    @testset "Transvection action correctness" begin
        i,j = 1,2
        r = Groups.Transvection(:ϱ,i,j)
        l = Groups.Transvection(:λ,i,j)

        (t::Groups.Transvection)(v::Tuple) = Groups.evaluate!(v, t, A4)

        @test      r(deepcopy(D)) == (a*b,   b, c, d)
        @test inv(r)(deepcopy(D)) == (a*b^-1,b, c, d)
        @test      l(deepcopy(D)) == (b*a,   b, c, d)
        @test inv(l)(deepcopy(D)) == (b^-1*a,b, c, d)

        i,j = 3,1
        r = Groups.Transvection(:ϱ,i,j)
        l = Groups.Transvection(:λ,i,j)
        @test      r(deepcopy(D)) == (a, b, c*a,   d)
        @test inv(r)(deepcopy(D)) == (a, b, c*a^-1,d)
        @test      l(deepcopy(D)) == (a, b, a*c,   d)
        @test inv(l)(deepcopy(D)) == (a, b, a^-1*c,d)

        i,j = 4,3
        r = Groups.Transvection(:ϱ,i,j)
        l = Groups.Transvection(:λ,i,j)
        @test      r(deepcopy(D)) == (a, b, c, d*c)
        @test inv(r)(deepcopy(D)) == (a, b, c, d*c^-1)
        @test      l(deepcopy(D)) == (a, b, c, c*d)
        @test inv(l)(deepcopy(D)) == (a, b, c, c^-1*d)

        i,j = 2,4
        r = Groups.Transvection(:ϱ,i,j)
        l = Groups.Transvection(:λ,i,j)
        @test      r(deepcopy(D)) == (a, b*d,   c, d)
        @test inv(r)(deepcopy(D)) == (a, b*d^-1,c, d)
        @test      l(deepcopy(D)) == (a, d*b,   c, d)
        @test inv(l)(deepcopy(D)) == (a, d^-1*b,c, d)
    end

    A = SpecialAutomorphismGroup(F4, maxrules=1000)

    @testset "AutomorphismGroup constructors" begin
        @test A isa Groups.AbstractFPGroup
        @test A isa AutomorphismGroup
        @test alphabet(A) isa Alphabet
        @test Groups.relations(A) isa Vector{<:Pair}
        @test sprint(show, A) == "automorphism group of free group on 4 generators"
    end

    @testset "Automorphisms: hash and evaluate" begin
        @test Groups.domain(gens(A, 1)) == D
        g, h = gens(A, 1), gens(A, 8)

        @test evaluate(g*h) == evaluate(h*g)
        @test (g*h).savedhash == zero(UInt)

        @test sprint(show, typeof(g)) == "Automorphism{FreeGroup{Symbol},…}"

        a = g*h
        b = h*g
        @test hash(a) != zero(UInt)
        @test hash(a) == hash(b)
        @test a.savedhash == b.savedhash

        @test length(unique([a,b])) == 1
        @test length(unique([g*h, h*g])) == 1

        # Not so simple arithmetic: applying starting on the left:
        # ϱ₁₂*ϱ₂₁⁻¹*λ₁₂*ε₂ == σ₂₁₃₄

        g = gens(A, 1)
        x1, x2, x3, x4 = Groups.domain(g)
        @test evaluate(g) == (x1*x2, x2, x3, x4)

        g = g*inv(gens(A, 4)) # ϱ₂₁
        @test evaluate(g) == (x1*x2, x1^-1, x3, x4)

        g = g*gens(A, 13)
        @test evaluate(g) == (x2, x1^-1, x3, x4)
    end

    @testset "Automorphisms: SAut(F₄)" begin
        N = 4
        G = SpecialAutomorphismGroup(FreeGroup(N))

        S = gens(G)
        @test S isa Vector{<:FPGroupElement{<:AutomorphismGroup{<:FreeGroup}}}

        @test length(S) == 2*N*(N-1)
        @test length(unique(S)) == length(S)

        S_sym = [S; inv.(S)]
        @test length(S_sym) == length(unique(S_sym))

        pushfirst!(S_sym, one(G))

        B_2 = [i*j for (i,j) in Base.product(S_sym, S_sym)]
        @test length(B_2) == 2401
        @test length(unique(B_2)) == 1777

        @test all(g->isone(inv(g)*g), B_2)
        @test all(g->isone(g*inv(g)), B_2)
    end

    @testset "Forward evaluate" begin
        N = 3
        F = FreeGroup(N)
        G = SpecialAutomorphismGroup(F)

        a = gens(G, 1) # ϱ₁₂

        f = gens(F)

        @test a(f[1]) == f[1]*f[2]
        @test all(a(f[i]) == f[i] for i in 2:length(f))

        S = let s = gens(G)
            [s; inv.(s)]
        end

        @test all(
            map(first(Groups.wlmetric_ball(S, radius=2))) do g
                lm = Groups.LettersMap(g)
                img = evaluate(g)

                fimg = [F(lm[first(word(s))]) for s in gens(F)]

                succeeded = all(img .== fimg)
                @assert succeeded "forward evaluation of $(word(g)) failed: \n img=$img\n fimg=$(tuple(fimg...))"
                succeeded
            end
        )
    end

    @testset "GroupsCore conformance" begin
        test_Group_interface(A)
        g = A(rand(1:length(alphabet(A)), 10))
        h = A(rand(1:length(alphabet(A)), 10))

        test_GroupElement_interface(g, h)
    end

end
