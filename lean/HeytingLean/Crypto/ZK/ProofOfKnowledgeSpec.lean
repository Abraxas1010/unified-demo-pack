import Mathlib

/-!
# Proof-of-knowledge (PoK) interface (spec-only)

This file defines a small, relation-based proof-of-knowledge interface with **soundness**.
It is intentionally proof-light and makes no cryptographic security claims (e.g. ZK, HVZK,
extractability under PPT assumptions, etc.).

We also provide a trivial, axiom-free constructor: the “proof” *is* the witness.
-/

namespace HeytingLean.Crypto.ZK

/-!
## Relation carrier
-/

structure Relation (Stmt Wit : Type) where
  holds : Stmt → Wit → Prop

/-!
## Non-interactive PoK (soundness-only)
-/

structure PoK (Stmt Wit Proof : Type) (R : Relation Stmt Wit) where
  prove : (s : Stmt) → (w : Wit) → R.holds s w → Proof
  verify : Stmt → Proof → Bool
  sound : ∀ s p, verify s p = true → ∃ w, R.holds s w

/-!
## Trivial PoK: proof carries the witness
-/

def witnessPoK {Stmt Wit : Type} (R : Relation Stmt Wit)
    [hdec : ∀ s w, Decidable (R.holds s w)] : PoK Stmt Wit Wit R where
  prove := fun _s w _hw => w
  verify := fun s w => decide (R.holds s w)
  sound := by
    intro s p hp
    refine ⟨p, ?_⟩
    have : decide (R.holds s p) = true := by
      simpa using hp
    exact (Bool.decide_iff (R.holds s p)).1 this

end HeytingLean.Crypto.ZK
