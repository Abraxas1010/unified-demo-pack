import Mathlib

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Concrete (but statement-first) lattice problem carriers

This file defines *typed carriers* for the main lattice problems referenced by the PQC bridge
work in `WIP/pqc_lattice/`.

Scope/intent:
- We commit only to **algebraic shapes** (matrices/vectors over `ZMod q`).
- We do **not** model distributions, PPT, or game-based security here.
- We keep parameters explicit and leave side conditions (e.g. `q > 1`) to later layers.
-/

abbrev Zq (q : Nat) : Type := ZMod q

abbrev ZVec (n q : Nat) : Type := Fin n → Zq q

abbrev ZMat (m n q : Nat) : Type := Matrix (Fin m) (Fin n) (Zq q)

/-- Basic LWE problem signature (statement-first). -/
structure LWEParams where
  n : Nat
  m : Nat
  q : Nat
  deriving Repr, DecidableEq

structure LWEInstance (P : LWEParams) where
  /-- Public matrix. -/
  A : ZMat P.m P.n P.q
  /-- Public RHS vector. -/
  b : ZVec P.m P.q
  deriving Repr, DecidableEq, Inhabited

/-- Coefficient-vector carrier for “ring elements” (later: `ZMod q[X]/(Φ)` etc). -/
abbrev Poly (n q : Nat) : Type := Fin n → Zq q

/-- Module-vector carrier: `k` coefficients-vectors of length `n`. -/
abbrev ModVec (k n q : Nat) : Type := Fin k → Poly n q

/-- Module-matrix carrier: `k×k` coefficients-vectors of length `n`. -/
abbrev ModMat (k n q : Nat) : Type := Matrix (Fin k) (Fin k) (Poly n q)

/-- Module-LWE problem signature (statement-first; matches ML-KEM/ML-DSA assumption families). -/
structure MLWEParams where
  n : Nat
  q : Nat
  k : Nat
  deriving Repr, DecidableEq

structure MLWEInstance (P : MLWEParams) where
  /-- Public module matrix. -/
  A : ModMat P.k P.n P.q
  /-- Public module RHS vector. -/
  b : ModVec P.k P.n P.q
  deriving Repr, DecidableEq, Inhabited

/-- SIS problem signature (statement-first). -/
structure SISParams where
  n : Nat
  m : Nat
  q : Nat
  deriving Repr, DecidableEq

end Lattice
end Crypto
end HeytingLean
