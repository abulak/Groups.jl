export WreathProduct, WreathProductElem

###############################################################################
#
#   WreathProduct / WreathProductElem
#
###############################################################################

doc"""
    WreathProduct <: Group
> Implements Wreath product of a group N by permutation (sub)group P < Sₖ,
> usually written as $N \wr P$.
> The multiplication inside wreath product is defined as
>    (n, σ) * (m, τ) = (n*ψ(σ)(m), σ*τ),
> where ψ:P → Aut(Nᵏ) is the permutation representation of Sₖ restricted to P.

# Arguments:
* `::Group` : the single factor of group N
* `::PermutationGroup` : full PermutationGroup
"""
immutable WreathProduct{T<:Group} <: Group
   N::DirectProductGroup{T}
   P::PermGroup

   function WreathProduct(G::Group, P::PermGroup)
      N = DirectProductGroup(G, P.n)
      return new(N, P)
   end
end

immutable WreathProductElem{T<:GroupElem} <: GroupElem
   n::DirectProductGroupElem{T}
   p::perm
   # parent::WreathProduct

   function WreathProductElem(n::DirectProductGroupElem, p::perm,
      check::Bool=true)
      if check
         length(n.elts) == parent(p).n || throw("Can't form WreathProductElem: lengths differ")
      end
      return new(n, p)
   end
end

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type{T<:Group}(G::WreathProduct{T}) =
   WreathProductElem{G.N.n, elem_type(T)}

parent_type{T<:GroupElem}(::WreathProductElem{T}) =
   WreathProduct{parent_type(T)}

parent(g::WreathProductElem) = WreathProduct(parent(g.n[1]), parent(g.p))

###############################################################################
#
#   WreathProduct / WreathProductElem constructors
#
###############################################################################

WreathProduct{T<:Group}(G::T, P::PermGroup) = WreathProduct{T}(G, P)

WreathProductElem{T<:GroupElem}(n::DirectProductGroupElem{T},
   p::perm, check::Bool=true) = WreathProductElem{T}(n, p, check)

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

function (G::WreathProduct)(g::WreathProductElem)
   n = try
      G.N(g.n)
   catch
      throw("Can't coerce $(g.n) to $(G.N) factor of $G")
   end
   p = try
      G.P(g.p)
   catch
      throw("Can't coerce $(g.p) to $(G.P) factor of $G")
   end
   elt = WreathProductElem(n, p)
   # elt.parent = G
   return elt
end

doc"""
    (G::WreathProduct)(n::DirectProductGroupElem, p::perm)
> Creates an element of wreath product `G` by coercing `n` and `p` to `G.N` and
> `G.P`, respectively.

"""
function (G::WreathProduct)(n::DirectProductGroupElem, p::perm)
   result = WreathProductElem(n,p)
   # result.parent = G
   return result
end

(G::WreathProduct)() = WreathProductElem(G.N(), G.P(), false)

doc"""
    (G::WreathProduct)(p::perm)
> Returns the image of permutation `p` in `G` via embedding `p -> (id,p)`.

"""
(G::WreathProduct)(p::perm) = G(G.N(), p)

doc"""
    (G::WreathProduct)(n::DirectProductGroupElem)
> Returns the image of `n` in `G` via embedding `n -> (n,())`. This is the
> embedding that makes sequence `1 -> N -> G -> P -> 1` exact.

"""
(G::WreathProduct)(n::DirectProductGroupElem) = G(n, G.P())

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function deepcopy_internal(g::WreathProductElem, dict::ObjectIdDict)
   return WreathProductElem(deepcopy(g.n), deepcopy(g.p), false)
end

function hash(G::WreathProduct, h::UInt)
   return hash(G.N, hash(G.P, hash(WreathProduct, h)))
end

function hash(g::WreathProductElem, h::UInt)
   return hash(g.n, hash(g.p, hash(parent(g), h)))
end

###############################################################################
#
#   String I/O
#
###############################################################################

function show(io::IO, G::WreathProduct)
   print(io, "Wreath Product of $(G.N.group) by $(G.P)")
end

function show(io::IO, g::WreathProductElem)
   print(io, "($(g.n)≀$(g.p))")
end

###############################################################################
#
#   Comparison
#
###############################################################################

function (==)(G::WreathProduct, H::WreathProduct)
   G.N == H.N || return false
   G.P == H.P || return false
   return true
end

function (==)(g::WreathProductElem, h::WreathProductElem)
   g.n == h.n || return false
   g.p == h.p || return false
   return true
end

###############################################################################
#
#   Group operations
#
###############################################################################

doc"""
    *(g::WreathProductElem, h::WreathProductElem)
> Return the wreath product group operation of elements, i.e.
>
> g*h = (g.n*g.p(h.n), g.p*h.p),
>
> where g.p(h.n) denotes the action of `g.p::perm` on
> `h.n::DirectProductGroupElem` via standard permutation of coordinates.
"""
function *(g::WreathProductElem, h::WreathProductElem)
   w = DirectProductGroupElem((h.n).elts[inv(g.p).d])
   return WreathProductElem(g.n*w, g.p*h.p, false)
end

doc"""
    inv(g::WreathProductElem)
> Returns the inverse of element of a wreath product, according to the formula
>   g^-1 = (g.n, g.p)^-1 = (g.p^-1(g.n^-1), g.p^-1).
"""
function inv(g::WreathProductElem)
   G = parent(g)
   w = G.N(inv(g.n).elts[g.p.d])
   return G(w, inv(g.p))
end

###############################################################################
#
#   Misc
#
###############################################################################

matrix_repr(g::WreathProductElem) = Any[matrix_repr(g.p) g.n]

function elements(G::WreathProduct)
   iter = Base.product(collect(elements(G.N)), collect(elements(G.P)))
   return (G(n)*G(p) for (n,p) in iter)
end

order(G::WreathProduct) = order(G.P)*order(G.N)
