import Base: ×

export DirectProductGroup, DirectProductGroupElem

###############################################################################
#
#   DirectProductGroup / DirectProductGroupElem
#
###############################################################################

doc"""
   DirectProductGroup(factors::Vector{Group}) <: Group
Implements direct product of groups as vector factors. The group operation is
`*` distributed component-wise, with component-wise identity as neutral element.
"""

immutable DirectProductGroup{T<:Group} <: Group
   factors::Vector{T}
end

immutable DirectProductGroupElem{T<:GroupElem} <: GroupElem
   elts::Vector{T}
end

###############################################################################
#
#   Type and parent object methods
#
###############################################################################

elem_type{T<:Group}(G::DirectProductGroup{T}) = DirectProductGroupElem{elem_type(first(G.factors))}

parent_type(::Type{DirectProductGroupElem}) = DirectProductGroup

parent(g::DirectProductGroupElem) = DirectProductGroup([parent(h) for h in g.elts])

###############################################################################
#
#   DirectProductGroup / DirectProductGroupElem constructors
#
###############################################################################

end

DirectProductGroup{T<:Group}(G::T, H::T) = DirectProductGroup{T}([G, H])

×(G::Group, H::Group) = DirectProductGroup([G,H])

###############################################################################
#
#   Parent object call overloads
#
###############################################################################

(G::DirectProductGroup)() = G([H() for H in G.factors])

(G::DirectProductGroup)(g::DirectProductGroupElem) = G(g.elts)

doc"""
    (G::DirectProductGroup)(a::Vector; checked=true)
> Constructs element of the direct product group `G` by coercing each element
> of vector `a` to the corresponding factor of `G`. If `checked` flag is set to
> `false` no checks on the correctness are performed.

"""
function (G::DirectProductGroup){T<:GroupElem}(a::Vector{T})
   length(a) == length(G.factors) || throw("Cannot coerce $a to $G: they have
      different number of factors")
   @assert elem_type(first(G.factors)) == T
   return DirectProductGroupElem(a)
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function deepcopy_internal(g::DirectProductGroupElem, dict::ObjectIdDict)
   G = parent(g)
   return G(deepcopy(g.elts))
end

function hash(G::DirectProductGroup, h::UInt)
   return hash(G.factors, hash(G.operations, hash(DirectProductGroup,h)))
end

function hash(g::DirectProductGroupElem, h::UInt)
   return hash(g.elts, hash(g.parent, hash(DirectProductGroupElem, h)))
end

doc"""
    eye(G::DirectProductGroup)
> Return the identity element for the given direct product of groups.

"""
eye(G::DirectProductGroup) = G()

###############################################################################
#
#   String I/O
#
###############################################################################

function show(io::IO, G::DirectProductGroup)
    println(io, "Direct product of groups")
    join(io, G.factors, ", ", " and ")
end

function show(io::IO, g::DirectProductGroupElem)
    print(io, "("*join(g.elts,",")*")")
end

###############################################################################
#
#   Comparison
#
###############################################################################

function (==)(G::DirectProductGroup, H::DirectProductGroup)
    G.factors == H.factors || return false
    G.operations == H.operations || return false
    return true
end

doc"""
    ==(g::DirectProductGroupElem, h::DirectProductGroupElem)
> Return `true` if the given elements of direct products are equal, otherwise return `false`.

"""
function (==)(g::DirectProductGroupElem, h::DirectProductGroupElem)
    parent(g) == parent(h) || return false
    g.elts == h.elts || return false
    return true
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function direct_mult(g::DirectProductGroupElem, h::DirectProductGroupElem)
    parent(g) == parent(h) || throw("Can't multiply elements from different groups: $g, $h")
    G = parent(g)
    return G([op(a,b)  for (op,a,b) in zip(G.operations, g.elts, h.elts)])
end

doc"""
    *(g::DirectProductGroupElem, h::DirectProductGroupElem)
> Return the direct-product group operation of elements, i.e. component-wise
> operation as defined by `operations` field of the parent object.

"""
(*)(g::DirectProductGroupElem, h::DirectProductGroupElem) = direct_mult(g,h)

###############################################################################
#
#   Inversion
#
###############################################################################

doc"""
    inv(g::DirectProductGroupElem)
> Return the inverse of the given element in the direct product group.

"""
# TODO: dirty hack around `+` operation
function inv(g::DirectProductGroupElem)
    G = parent(g)
    return G([(op == (*) ? inv(elt): -elt) for (op,elt) in zip(G.operations, g.elts)])
end

###############################################################################
#
#   Misc
#
###############################################################################

doc"""
    elements(G::DirectProductGroup)
> Returns `Task` that produces all elements of group `G` (provided that factors
> implement the elements function).

"""
# TODO: can Base.product handle generators?
#   now it returns nothing's so we have to collect ellements...
function elements(G::DirectProductGroup)
    cartesian_prod = Base.product([collect(elements(H)) for H in G.factors]...)
    return (G(collect(elt)) for elt in cartesian_prod)
end

doc"""
    order(G::DirectProductGroup)
> Returns the order (number of elements) in the group.

"""
order(G::DirectProductGroup) = prod([order(H) for H in G.factors])
