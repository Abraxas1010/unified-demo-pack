import Mathlib.Data.Real.Basic
import Mathlib.Order.Heyting.Basic
import HeytingLean.LoF.CryptoSheaf.Quantum.Valuation

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum
namespace Examples

open Classical

/-- A certified 0/1 valuation on Prop as a Heyting algebra. -/
noncomputable def propValuation : Quantum.Valuation Prop where
  v := fun p => if p then (1 : ℝ) else 0
  mono := by
    intro x y hxy
    cases x <;> cases y
    · simp
    · simp [zero_le_one]
    · exact (hxy trivial).elim
    · simp
  submod := by
    intro x y
    cases x <;> cases y
    · simp
    · simp [zero_le_one]
    · simp [zero_le_one]
    · simp
  norm_top := by simp
  norm_bot := by simp

@[simp] lemma propValuation_v_true : propValuation.v True = 1 := by
  classical; simp [propValuation]
@[simp] lemma propValuation_v_false : propValuation.v False = 0 := by
  classical; simp [propValuation]

end Examples
end Quantum
end CryptoSheaf
end LoF
end HeytingLean

