import Mathlib.Data.Real.Basic
import Mathlib.Order.Heyting.Basic
import HeytingLean.LoF.CryptoSheaf.Quantum.Valuation

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum
namespace Examples

open Classical

/-- A certified 0/1 valuation on Bool as a Heyting algebra. -/
def boolValuation : Quantum.Valuation Bool where
  v := fun b => if b then (1 : ℝ) else 0
  mono := by
    intro x y hxy
    cases x <;> cases y
    · simp
    · simp
    · -- true ≤ false is impossible in Bool's order
      -- Convert to `⊤ ≤ ⊥` and use `top_le_iff` to derive `false = true`.
      have htf : (⊤ : Bool) ≤ (⊥ : Bool) := by simpa using hxy
      have : false = true := by
        -- `top_le_iff.mp : ⊤ ≤ a → a = ⊤`
        simpa using (top_le_iff.mp htf)
      exact (Bool.false_ne_true this).elim
    · simp
  submod := by
    intro x y
    cases x <;> cases y <;> simp
  norm_top := by simp
  norm_bot := by simp

@[simp] lemma boolValuation_v_true : boolValuation.v True = 1 := rfl
@[simp] lemma boolValuation_v_false : boolValuation.v False = 0 := rfl

/-- A computable Nat companion aligned with `boolValuation`. -/
def boolValuationNat (b : Bool) : Nat := if b then 1 else 0

@[simp] lemma boolValuation_v_coeNat (b : Bool) : boolValuation.v b = (boolValuationNat b : ℝ) := by
  cases b <;> simp [boolValuation, boolValuationNat]

/-- On the miniature cover used by the contextuality demo, the numeric bound holds. -/
theorem boolValuation_bound : (boolValuation.v False) ≤ min (boolValuation.v True) (boolValuation.v False) := by
  simp [boolValuation]

end Examples
end Quantum
end CryptoSheaf
end LoF
end HeytingLean
