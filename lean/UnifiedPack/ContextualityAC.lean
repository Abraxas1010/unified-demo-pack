import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import HeytingLean.LoF.CryptoSheaf.Quantum.ContextualitySite
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel
import HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.ContextualityBridge

namespace UnifiedPack

open Classical
open HeytingLean.LoF.CryptoSheaf.Quantum
open Finset

set_option linter.unnecessarySimpa false

/-- In the 2‑point context `C_ac`, any point is either `a_in_ac` or `c_in_ac`. -/
private lemma mem2_ac (x : MeasIn C_ac) : x = a_in_ac ∨ x = c_in_ac := by
  classical
  have hx : x.1 = a ∨ x.1 = c := by
    have hx2 := x.2
    have : x.1 ∈ insert a ({c} : Finset Meas) := by simpa [C_ac] using hx2
    rcases mem_insert.mp this with hxa | hxc
    · exact Or.inl hxa
    · have hx' : x.1 = c := by exact mem_singleton.mp hxc; exact Or.inr hx'
  rcases hx with hxa | hxc
  · left; apply Subtype.ext; exact hxa
  · right; apply Subtype.ext; exact hxc

/-- Boolean helper: if `x ≠ y` then `y = !x`. -/
private theorem bool_ne_implies_neg {x y : Bool} : x ≠ y → y = !x := by
  intro h; cases x <;> cases y <;> try (cases h rfl); simp

@[simp] private lemma c_in_ac_ne_a_in_ac : c_in_ac ≠ a_in_ac := by
  intro h; have : (c : Meas) = (a : Meas) := congrArg Subtype.val h; exact (by decide : c ≠ a) this

/-- AC support is in bijection with `Bool` via flipping at `a`. -/
noncomputable def equivSupportAC : {s // s ∈ supportAC} ≃ Bool :=
{ toFun := fun p => p.1 a_in_ac,
  invFun := fun v => ⟨(fun x => if x = a_in_ac then v else !v), by
    classical; cases v <;> simp [c_in_ac_ne_a_in_ac, HeytingLean.LoF.CryptoSheaf.Quantum.supportAC]
  ⟩,
  left_inv := by
    intro p; cases p with
    | mk s hs =>
      apply Subtype.ext; funext x; classical
      rcases mem2_ac x with hxa | hxc
      · simp [hxa]
      · have hne : s a_in_ac ≠ s c_in_ac := by simpa [HeytingLean.LoF.CryptoSheaf.Quantum.supportAC] using hs
        have : s c_in_ac = ! (s a_in_ac) := bool_ne_implies_neg hne
        simp [hxc, this]
  , right_inv := by intro v; simp }

theorem supportAC_size_two :
  HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.supportSize (supportAC) = 2 := by
  classical
  simpa [HeytingLean.LoF.CryptoSheaf.Quantum.Entropy.supportSize] using
    Fintype.card_congr (equivSupportAC)

end UnifiedPack

