## Hashing

equality_data(g::AbstractFPGroupElement) = (normalform!(g); word(g))

bitget(h::UInt, n::Int) = Bool((h & (1 << n)) >> n)
bitclear(h::UInt, n::Int) = h & ~(1 << n)
bitset(h::UInt, n::Int) = h | (1 << n)
bitset(h::UInt, v::Bool, n::Int) = v ? bitset(h, n) : bitclear(h, n)

# We store hash of a word in field `savedhash` to use it as cheap proxy to
# determine non-equal words. Additionally bits of `savehash` store boolean
# information as follows
# * `savedhash & 1` (the first bit): is word in normal form?
# * `savedhash & 2` (the second bit): is the hash valid?
const __BITFLAGS_MASK = ~(~(UInt(0)) << 2)

isnormalform(g::AbstractFPGroupElement) = bitget(g.savedhash, 0)
_isvalidhash(g::AbstractFPGroupElement) = bitget(g.savedhash, 1)

_setnormalform(h::UInt, v::Bool) = bitset(h, v, 0)
_setvalidhash(h::UInt, v::Bool) = bitset(h, v, 1)

_setnormalform!(g::AbstractFPGroupElement, v::Bool) = g.savedhash = _setnormalform(g.savedhash, v)
_setvalidhash!(g::AbstractFPGroupElement, v::Bool) = g.savedhash = _setvalidhash(g.savedhash, v)

# To update hash use this internal method, possibly only after computing the
# normal form of `g`:
function _update_savedhash!(g::AbstractFPGroupElement, data)
    h = hash(data, hash(parent(g)))
    h = (h << count_ones(__BITFLAGS_MASK)) | (__BITFLAGS_MASK & g.savedhash)
    g.savedhash = _setvalidhash(h, true)
    return g
end

function Base.hash(g::AbstractFPGroupElement, h::UInt)
    _isvalidhash(g) || _update_savedhash!(g, equality_data(g))
    return hash(g.savedhash >> count_ones(__BITFLAGS_MASK), h)
end

function Base.copyto!(res::AbstractFPGroupElement, g::AbstractFPGroupElement)
    @assert parent(res) === parent(g)
    resize!(word(res), length(word(g)))
    copyto!(word(res), word(g))
    res.savedhash = g.savedhash
    return res
end
