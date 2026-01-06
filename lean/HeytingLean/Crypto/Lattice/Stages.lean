import HeytingLean.LoF.Nucleus
import HeytingLean.Logic.StageSemantics

/-!
# Dial-Parameterized Constant-Time Lattice Ops (Algebraic CT)

Define lattice-like operations on the Heyting core `Ω_R` that operate in the fixed locus via
interiorised join/implication, and show they are monotone (branch-free in the algebraic model).
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace Stages

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

variable (R : Reentry α)

/-- Meet in `Ω_R` (plain Heyting meet). -/
def ctMeet (a b : R.Omega) : R.Omega := a ⊓ b

/-- Interiorised join in `Ω_R`. -/
def ctJoin (a b : R.Omega) : R.Omega :=
  Reentry.Omega.mk (R := R) (R ((a : α) ⊔ (b : α))) (by simp)

/-- Interiorised implication in `Ω_R`. -/
def ctImp (a b : R.Omega) : R.Omega :=
  Reentry.Omega.mk (R := R) (R ((a : α) ⇨ (b : α))) (by simp)

@[simp] lemma ctMeet_coe (a b : R.Omega) :
    ((ctMeet (R := R) a b : R.Omega) : α) = (a : α) ⊓ (b : α) := rfl

@[simp] lemma ctJoin_coe (a b : R.Omega) :
    ((ctJoin (R := R) a b : R.Omega) : α) = R ((a : α) ⊔ (b : α)) := rfl

@[simp] lemma ctImp_coe (a b : R.Omega) :
    ((ctImp (R := R) a b : R.Omega) : α) = R ((a : α) ⇨ (b : α)) := rfl

/-- Monotonicity of `ctJoin` in the left argument. -/
lemma ctJoin_mono_left {a a' b : R.Omega}
    (ha : (a : α) ≤ (a' : α)) :
    ctJoin (R := R) a b ≤ ctJoin (R := R) a' b := by
  change (R ((a : α) ⊔ (b : α))) ≤ R ((a' : α) ⊔ (b : α))
  have h1 : (a : α) ≤ (a' : α) ⊔ (b : α) :=
    le_trans ha (le_sup_of_le_left le_rfl)
  have h2 : (b : α) ≤ (a' : α) ⊔ (b : α) :=
    le_sup_of_le_right le_rfl
  have hsup : (a : α) ⊔ (b : α) ≤ (a' : α) ⊔ (b : α) :=
    sup_le h1 h2
  exact R.monotone hsup

/-- Monotonicity of `ctJoin` in the right argument. -/
lemma ctJoin_mono_right {a b b' : R.Omega}
    (hb : (b : α) ≤ (b' : α)) :
    ctJoin (R := R) a b ≤ ctJoin (R := R) a b' := by
  change (R ((a : α) ⊔ (b : α))) ≤ R ((a : α) ⊔ (b' : α))
  have h1 : (a : α) ≤ (a : α) ⊔ (b' : α) :=
    le_sup_of_le_left le_rfl
  have h2 : (b : α) ≤ (a : α) ⊔ (b' : α) :=
    le_trans hb (le_sup_of_le_right le_rfl)
  have hsup : (a : α) ⊔ (b : α) ≤ (a : α) ⊔ (b' : α) :=
    sup_le h1 h2
  exact R.monotone hsup

/-- Monotonicity of `ctMeet` in both arguments. -/
lemma ctMeet_mono_left {a a' b : R.Omega}
    (ha : (a : α) ≤ (a' : α)) :
    ctMeet (R := R) a b ≤ ctMeet (R := R) a' b := by
  change (a : α) ⊓ (b : α) ≤ (a' : α) ⊓ (b : α)
  exact le_inf (le_trans inf_le_left ha) inf_le_right

lemma ctMeet_mono_right {a b b' : R.Omega}
    (hb : (b : α) ≤ (b' : α)) :
    ctMeet (R := R) a b ≤ ctMeet (R := R) a b' := by
  change (a : α) ⊓ (b : α) ≤ (a : α) ⊓ (b' : α)
  exact le_inf inf_le_left (le_trans inf_le_right hb)

/-- Monotonicity of `ctImp` in the right argument. -/
lemma ctImp_mono_right {a b b' : R.Omega}
    (hb : (b : α) ≤ (b' : α)) :
    ctImp (R := R) a b ≤ ctImp (R := R) a b' := by
  change R ((a : α) ⇨ (b : α)) ≤ R ((a : α) ⇨ (b' : α))
  have : ((a : α) ⇨ (b : α)) ≤ ((a : α) ⇨ (b' : α)) := by
    exact himp_le_himp_right hb
  exact R.monotone this

/-- Fast (boolean) and constant-time (orthomodular) op bundles. -/
structure Ops where
  meet : R.Omega → R.Omega → R.Omega
  join : R.Omega → R.Omega → R.Omega
  imp  : R.Omega → R.Omega → R.Omega

def opsAtBoolean : Ops (R := R) :=
  { meet := ctMeet (R := R)
    join := ctJoin (R := R)
    imp  := ctImp  (R := R) }

def opsAtOrthomodular : Ops (R := R) :=
  { meet := ctMeet (R := R)
    join := ctJoin (R := R)
    imp  := ctImp  (R := R) }

abbrev fast_reduce := opsAtBoolean (R := R)
abbrev ct_reduce   := opsAtOrthomodular (R := R)

/-- CT lemma: ops are compositions of meet and interiorised joins/implications ⇒ monotone.
Branch-free here means no data-dependent control flow is needed in the algebraic model. -/
theorem ct_no_branch :
    (∀ a a' b, (a : α) ≤ (a' : α) →
      ctJoin (R := R) a b ≤ ctJoin (R := R) a' b)
    ∧ (∀ a b b', (b : α) ≤ (b' : α) →
      ctJoin (R := R) a b ≤ ctJoin (R := R) a b')
    ∧ (∀ a a' b, (a : α) ≤ (a' : α) →
      ctMeet (R := R) a b ≤ ctMeet (R := R) a' b)
    ∧ (∀ a b b', (b : α) ≤ (b' : α) →
      ctMeet (R := R) a b ≤ ctMeet (R := R) a b')
    ∧ (∀ a b b', (b : α) ≤ (b' : α) →
      ctImp (R := R) a b ≤ ctImp (R := R) a b') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a a' b ha; exact ctJoin_mono_left (R := R) (a := a) (a' := a') (b := b) ha
  · intro a b b' hb; exact ctJoin_mono_right (R := R) (a := a) (b := b) (b' := b') hb
  · intro a a' b ha; exact ctMeet_mono_left (R := R) (a := a) (a' := a') (b := b) ha
  · intro a b b' hb; exact ctMeet_mono_right (R := R) (a := a) (b := b) (b' := b') hb
  · intro a b b' hb; exact ctImp_mono_right (R := R) (a := a) (b := b) (b' := b') hb

end Stages
end Lattice
end Crypto
end HeytingLean

