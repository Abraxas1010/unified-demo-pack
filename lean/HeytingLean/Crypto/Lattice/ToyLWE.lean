import HeytingLean.Crypto.RNG.Seeded
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace ToyLWE

/-!
# Toy LWE-Style KEM (Executable Model)

This module is an **executable toy model** (tiny parameters) intended to validate wiring:
seeded RNG → keygen/encap/decap → shared-secret agreement.

It is **not** a cryptographic construction; it omits essential details (noise, encoding, CCA transforms).
-/

open HeytingLean.Crypto.RNG
open HeytingLean.Util

structure Params where
  n : Nat := 4
  q : Nat := 16
  deriving Repr, Inhabited

structure PublicKey where
  a : Array Nat
  b : Nat

structure SecretKey where
  s : Array Nat

structure Ciphertext where
  u : Array Nat
  v : Nat

structure SharedSecret where
  bytes : ByteArray

inductive Error where
  | invalidCiphertext
  deriving Repr, DecidableEq

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def baAppend (a b : ByteArray) : ByteArray :=
  mkBA (a.data ++ b.data)

private def baConcat (xs : List ByteArray) : ByteArray :=
  xs.foldl baAppend (mkBA #[])

private def modq (q x : Nat) : Nat :=
  if q == 0 then 0 else x % q

private def zipWith (f : Nat → Nat → Nat) (x y : Array Nat) : Array Nat := Id.run do
  let n := Nat.min x.size y.size
  let mut out : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (f x[i]! y[i]!)
  return out

private def addVec (q : Nat) (x y : Array Nat) : Array Nat :=
  zipWith (fun a b => modq q (a + b)) x y

private def mulScalar (q r : Nat) (x : Array Nat) : Array Nat :=
  x.map (fun a => modq q (a * r))

private def dot (q : Nat) (x y : Array Nat) : Nat :=
  let n := Nat.min x.size y.size
  let rec go (i acc : Nat) : Nat :=
    if h : i < n then
      let acc' := modq q (acc + x[i]! * y[i]!)
      go (i + 1) acc'
    else
      acc
  go 0 0

private def sampleVec (p : Params) (rng : SeededRNG) : Array Nat × SeededRNG :=
  let (bytes, rng') := SeededRNG.nextBytes rng p.n
  let v := bytes.data.map (fun b => modq p.q b.toNat)
  (v, rng')

private def sampleByte (rng : SeededRNG) : Nat × SeededRNG :=
  let (b, rng') := SeededRNG.nextBytes rng 1
  (b.data.getD 0 0 |>.toNat, rng')

private def vecToBytes (v : Array Nat) : ByteArray :=
  mkBA (v.map (fun x => UInt8.ofNat (x % 256)))

private def natToByte (x : Nat) : ByteArray :=
  mkBA #[UInt8.ofNat (x % 256)]

private def tagSs : ByteArray := ("toylwe:ss:" : String).toUTF8

private def deriveSS (p : Params) (u : Array Nat) (v m : Nat) : SharedSecret :=
  let payload := baConcat [tagSs, natToByte p.n, natToByte p.q, vecToBytes u, natToByte v, natToByte m]
  { bytes := SHA256.sha256Bytes payload }

def keygen (p : Params) (rng : SeededRNG) : PublicKey × SecretKey × SeededRNG :=
  let (a, rng1) := sampleVec p rng
  let (s, rng2) := sampleVec p rng1
  let b := dot p.q a s
  ({ a := a, b := b }, { s := s }, rng2)

def encap (p : Params) (pk : PublicKey) (rng : SeededRNG) :
    Ciphertext × SharedSecret × SeededRNG :=
  let (r0, rng1) := sampleByte rng
  let (m0, rng2) := sampleByte rng1
  let r := modq p.q r0
  let m := m0 % 2
  let u := mulScalar p.q r pk.a
  let half := p.q / 2
  let v := modq p.q (r * pk.b + m * half)
  let ss := deriveSS p u v m
  ({ u := u, v := v }, ss, rng2)

def decap (p : Params) (sk : SecretKey) (ct : Ciphertext) : Except Error SharedSecret := do
  if p.q == 0 || ct.u.size != p.n || sk.s.size != p.n then
    throw .invalidCiphertext
  let uv := dot p.q ct.u sk.s
  let w := modq p.q (ct.v + p.q - uv)
  let one := if w >= p.q / 4 && w < (3 * p.q) / 4 then 1 else 0
  return deriveSS p ct.u ct.v one

def roundTripOk (p : Params) (seed : ByteArray) : Bool :=
  let rng := SeededRNG.init seed
  let (pk, sk, rng1) := keygen p rng
  let (ct, ss1, _rng2) := encap p pk rng1
  match decap p sk ct with
  | .ok ss2 => ss1.bytes == ss2.bytes
  | .error _ => false

end ToyLWE
end Lattice
end Crypto
end HeytingLean

