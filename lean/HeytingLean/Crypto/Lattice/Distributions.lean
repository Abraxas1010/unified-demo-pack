import HeytingLean.Crypto.RNG.Seeded

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace Dist

open HeytingLean.Crypto.RNG

/-!
# Deterministic sampling façades (toy/executable)

This file provides simple **deterministic** samplers used by toy models and tests.

Notes:
- These are *not* cryptographically faithful to Kyber/Dilithium sampling.
- The goal is to replace the “all zeros” placeholders with total, stable APIs that can be used
  to build executable models and deterministic tests.
- For KAT parity, the C reference harnesses under `WIP/pqc_lattice/` remain authoritative.
-/

/-- Seed wrapper for deterministic sampling. -/
structure Seed where
  bytes : ByteArray
  deriving DecidableEq

abbrev Sample := Int

private def natOfBytesLE (bs : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut pow : Nat := 1
  for b in bs.data do
    acc := acc + pow * b.toNat
    pow := pow * 256
  return acc

private def popcountLow (x bits : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [0:bits] do
    if x.testBit i then
      acc := acc + 1
  return acc

/-!
## Byte/bit stream helpers

To align more closely with FIPS-style samplers, we treat the seeded RNG as a little-endian
bitstream so we can:
- consume exactly `2*eta` bits per CBD sample (no wasted padding bits), and
- implement unbiased `uniformMod` via rejection sampling on `k = ⌈log₂ q⌉` bits.
-/

private structure BitStream where
  rng : SeededRNG
  buf : Nat
  bits : Nat

private def bitstreamInit (s : Seed) : BitStream :=
  { rng := SeededRNG.init s.bytes, buf := 0, bits := 0 }

private def bitstreamTake (k : Nat) (st : BitStream) : Nat × BitStream := Id.run do
  let mut rng := st.rng
  let mut buf := st.buf
  let mut bits := st.bits
  while bits < k do
    let (bs, rng') := SeededRNG.nextBytes rng 1
    rng := rng'
    let b : Nat := (bs.get! 0).toNat
    buf := buf + b * (2 ^ bits)
    bits := bits + 8
  let mask : Nat := 2 ^ k
  let out := buf % mask
  buf := buf / mask
  bits := bits - k
  return (out, { rng := rng, buf := buf, bits := bits })

private def bitsNeeded (q : Nat) : Nat := Id.run do
  let mut bits : Nat := 0
  let mut pow : Nat := 1
  while pow < q do
    pow := pow * 2
    bits := bits + 1
  return bits

/-- Centered binomial sampler using `2*eta` bits per output.

Implementation: consume exactly `2*eta` bits from a little-endian bitstream and compute
`popcount(low eta bits) - popcount(next eta bits)`.
-/
def centeredBinomial (eta : Nat) (s : Seed) (n : Nat) : Array Sample := Id.run do
  let mut st := bitstreamInit s
  let mut out : Array Sample := Array.mkEmpty n
  for _i in [0:n] do
    let (x, st') := bitstreamTake (2 * eta) st
    st := st'
    let a := popcountLow x eta
    let b := popcountLow (x / (2 ^ eta)) eta
    out := out.push (Int.ofNat a - Int.ofNat b)
  return out

/-- Uniform sampler `0..q-1` using 32-bit little-endian blocks.

This uses rejection sampling on `k = ⌈log₂ q⌉` bits to avoid modulo bias.
-/
def uniformMod (q : Nat) (s : Seed) (n : Nat) : Array Sample := Id.run do
  if q ≤ 1 then
    return Array.replicate n 0
  let k := bitsNeeded q
  let mut st := bitstreamInit s
  let mut out : Array Sample := Array.mkEmpty n
  for _i in [0:n] do
    let mut y : Nat := q
    while y ≥ q do
      let (cand, st') := bitstreamTake k st
      st := st'
      y := cand
    out := out.push (Int.ofNat y)
  return out

end Dist
end Lattice
end Crypto
end HeytingLean
