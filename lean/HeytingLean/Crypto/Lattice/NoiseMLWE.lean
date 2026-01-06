import HeytingLean.Crypto.Lattice.NucleusBridge
import HeytingLean.Crypto.Lattice.Problems

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Noise-aware MLWE (v1.2 foundations)

This file introduces a **noise-aware** view of the (module-)LWE equation by attaching an explicit
error term `e` together with a correctness equation:

`b = A.mulVec s + e`.

This is intentionally *proof-light* and *axiom-free*: we provide interfaces that can be
instantiated later with concrete bounded-decoding algorithms and distributional assumptions.
-/

open scoped Classical

/-- Coarse coefficient bound for `ZMod q` elements (uses the canonical representative `0..q-1`). -/
def coeffBound {q : Nat} (x : Zq q) : Nat :=
  Int.natAbs (Int.ofNat x.val)

@[simp] theorem coeffBound_zero {q : Nat} : coeffBound (q := q) (0 : Zq q) = 0 := by
  simp [coeffBound]

/-!
## Noise-aware instance carrier
-/

/-- Noise-aware MLWE instance: explicit secret `s` and error `e` with `b = A*s + e`. -/
structure NoiseMLWEInstance (P : MLWEParams) where
  A : ModMat P.k P.n P.q
  s : ModVec P.k P.n P.q
  e : ModVec P.k P.n P.q
  b : ModVec P.k P.n P.q
  eqn : b = A.mulVec s + e

/-- Coefficient-wise boundedness predicate for module noise vectors, using `ZMod.val` (Nat reps). -/
def BoundedNatRep (P : MLWEParams) (β : Nat) (e : ModVec P.k P.n P.q) : Prop :=
  ∀ i j, coeffBound (e i j) ≤ β

theorem boundedNatRep_zero (P : MLWEParams) (β : Nat) : BoundedNatRep P β (0 : ModVec P.k P.n P.q) := by
  intro i j
  simp [coeffBound]

/-!
## Noise-aware recovery view
-/

/-- Public view for a noise-aware MLWE instance (public data is `⟨A,b⟩`, goal is to recover `s`). -/
def NoiseMLWEView (P : MLWEParams) : RecoveryView (NoiseMLWEInstance P) where
  Pub := MLWEInstance P
  encode := fun inst => { A := inst.A, b := inst.b }
  goalEq := fun x y => x.s = y.s

/-!
## BoundedNatRep decoding interface (statement-first)
-/

/-- Bounded decoding API: correctness required only on a declared instance set. -/
structure NoiseDecode (P : MLWEParams) (β : Nat) where
  decode : ModMat P.k P.n P.q → ModVec P.k P.n P.q → Option (ModVec P.k P.n P.q)
  instances : Set (NoiseMLWEInstance P) := Set.univ
  correct : ∀ inst, inst ∈ instances → BoundedNatRep P β inst.e → decode inst.A inst.b = some inst.s

/-!
## Toy instantiation: identity matrix + zero noise

This is a compile-coverage toy: if `A = 1` and `e = 0`, then `b = s`, so returning `b` recovers `s`.
-/

def idOnlyInstances (P : MLWEParams) : Set (NoiseMLWEInstance P) :=
  { inst | inst.A = 1 ∧ inst.e = 0 }

def idOnlyDecode (P : MLWEParams) : NoiseDecode P 0 where
  decode := fun _A b => some b
  instances := idOnlyInstances P
  correct := by
    intro inst hinst _hbounded
    rcases hinst with ⟨hA, he⟩
    have hb : inst.b = inst.s := by
      -- From `b = A*s + e`, with `A = 1` and `e = 0`.
      simpa [hA, he] using inst.eqn
    -- The decoder returns `some b`.
    simp [hb]

end Lattice
end Crypto
end HeytingLean
