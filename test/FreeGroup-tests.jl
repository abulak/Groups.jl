@testset "Groups.FreeSymbols" begin
   s = Groups.FreeSymbol(:s)
   t = Groups.FreeSymbol(:t)

   @testset "constructors" begin
      @test isa(Groups.FreeSymbol(:aaaaaaaaaaaaaaaa), Groups.GSymbol)
      @test Groups.FreeSymbol(:abc).pow == 1
      @test isa(s, Groups.FreeSymbol)
      @test isa(t, Groups.FreeSymbol)
   end
   @testset "eltary functions" begin
      @test length(s) == 1
      @test Groups.change_pow(s, 0) == Groups.change_pow(t, 0)
      @test length(Groups.change_pow(s, 0)) == 0
      @test inv(s).pow == -1
      @test Groups.FreeSymbol(:s, 3) == Groups.change_pow(s, 3)
      @test Groups.FreeSymbol(:s, 3) != Groups.FreeSymbol(:t, 3)
      @test Groups.change_pow(inv(s), -3) == inv(Groups.change_pow(s, 3))
   end
   @testset "powers" begin
      s⁴ = Groups.change_pow(s,4)
      @test s⁴.pow == 4
      @test Groups.change_pow(s, 4) == Groups.FreeSymbol(:s, 4)
   end
end

@testset "FreeGroupSymbols manipulation" begin
   s = Groups.FreeSymbol("s")
   t = Groups.FreeSymbol(:t, -2)

   @test isa(Groups.GroupWord(s), Groups.GWord{Groups.FreeSymbol})
   @test isa(Groups.GroupWord(s), FreeGroupElem)
   @test isa(FreeGroupElem(s), Groups.GWord)
   @test isa(convert(FreeGroupElem, s), Groups.GWord)
   @test isa(convert(FreeGroupElem, s), FreeGroupElem)
   @test isa(Vector{FreeGroupElem}([s,t]), Vector{FreeGroupElem})
   @test length(FreeGroupElem(s)) == 1
   @test length(FreeGroupElem(t)) == 2

end

@testset "FreeGroup" begin
   @test isa(FreeGroup(["s", "t"]), AbstractAlgebra.Group)
   G = FreeGroup(["s", "t"])

   @testset "elements constructors" begin
      @test isa(one(G), FreeGroupElem)
      @test eltype(G.gens) == Groups.FreeSymbol
      @test length(G.gens) == 2
      @test eltype(gens(G)) == FreeGroupElem
      @test length(gens(G)) == 2
   end

   s, t = gens(G)

   @testset "internal arithmetic" begin

      @test (s*s).symbols == (s^2).symbols
      @test hash([t^1,s^1]) == hash([t^2*inv(t),s*inv(s)*s])

      t_symb = Groups.FreeSymbol(:t)
      tt = deepcopy(t)
      @test string(Groups.rmul!(tt, tt, inv(tt))) == "(id)"
      tt = deepcopy(t)
      @test string(Groups.lmul!(tt, tt, inv(tt))) == "(id)"

      tt = deepcopy(t)
      push!(tt, inv(t_symb))
      @test string(tt) == "t*t^-1"
      tt = deepcopy(t)
      pushfirst!(tt, inv(t_symb))
      @test string(tt) == "t^-1*t"

      tt = deepcopy(t)
      append!(tt, inv(t))
      @test string(tt) == "t*t^-1"

      tt = deepcopy(t)
      prepend!(tt, inv(t))
      @test string(tt) == "t^-1*t"

      tt = deepcopy(t)
      append!(tt, s, inv(t))
      @test string(tt) == "t*s*t^-1"
   end

   @testset "reductions" begin
      @test length(one(G).symbols) == 0
      @test length((one(G)*one(G)).symbols) == 0
      @test one(G) == one(G)*one(G)
      w = deepcopy(s)
      push!(Groups.syllables(w), (s^-1).symbols[1])
      @test Groups.reduce!(w) == one(parent(w))
      o = (t*s)^3
      @test o == t*s*t*s*t*s
      p = (t*s)^-3
      @test p == s^-1*t^-1*s^-1*t^-1*s^-1*t^-1
      @test o*p == one(parent(o*p))
      w = FreeGroupElem([o.symbols..., p.symbols...])
      w.parent = G
      @test Groups.reduce!(w).symbols ==Vector{Groups.FreeSymbol}([])
   end

   @testset "Group operations" begin
      @test parent(s) == G
      @test parent(s) === parent(deepcopy(s))
      @test isa(s*t, FreeGroupElem)
      @test parent(s*t) == parent(s^2)
      @test s*s == s^2
      @test inv(s*s) == inv(s^2)
      @test inv(s)^2 == inv(s^2)
      @test inv(s)*inv(s) == inv(s^2)
      @test inv(s*t) == inv(t)*inv(s)
      w = s*t*s^-1
      @test inv(w) == s*t^-1*s^-1
      @test (t*s*t^-1)^10 == t*s^10*t^-1
      @test (t*s*t^-1)^-10 == t*s^-10*t^-1
   end

   @testset "replacements" begin
      a = Groups.FreeSymbol(:a)
      b = Groups.FreeSymbol(:b)
      @test Groups.issubsymbol(a, Groups.change_pow(a,2)) == true
      @test Groups.issubsymbol(a, Groups.change_pow(a,-2)) == false
      @test Groups.issubsymbol(b, Groups.change_pow(a,-2)) == false
      @test Groups.issubsymbol(inv(b), Groups.change_pow(b,-2)) == true

      c = s*t*s^-1*t^-1
      @test findfirst(s^-1*t^-1, c) == 3
      @test findnext(s^-1*t^-1, c*s^-1,3) == 3
      @test findnext(s^-1*t^-1, c*s^-1*t^-1,4) == 5
      @test findfirst(c, c*t) === nothing
      w = s*t*s^-1
      subst = Dict{FreeGroupElem, FreeGroupElem}(w => s^1, s*t^-1 => t^4)
      @test Groups.replace(c, s*t=>one(G)) == s^-1*t^-1
      @test Groups.replace(c, w=>subst[w]) == s*t^-1
      @test Groups.replace(s*c*t^-1, w=>subst[w]) == s^2*t^-2
      @test Groups.replace(t*c*t, w=>subst[w]) == t*s
      @test Groups.replace(s*c*s*c*s, subst) == s*t^4*s*t^4*s

      G = FreeGroup(["x", "y"])
      x,y = gens(G)

      @test Groups.replace(x*y^9, y^2=>y) == x*y^5
      @test Groups.replace(x^3, x^2=>y) == x*y
      @test Groups.replace(y*x^3*y, x^2=>y) == y*x*y^2
   end
end
