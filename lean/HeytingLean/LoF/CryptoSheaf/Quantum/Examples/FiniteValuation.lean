import Mathlib.Data.Real.Basic
-- We use a simple numeric proxy; a certified Valuation instance can replace this later.

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum
namespace Examples

open Classical

/-- A concrete 0/1 numeric proxy on Bool used as a valuation in demos. -/
def boolV : Bool → ℝ := fun b => if b then (1 : ℝ) else 0

@[simp] lemma boolV_true : boolV True = 1 := rfl
@[simp] lemma boolV_false : boolV False = 0 := rfl

/-- Miniature bound for the demo cover. -/
theorem boolV_bound : (boolV False) ≤ min (boolV True) (boolV False) := by
  simp [boolV]

end Examples
end Quantum
end CryptoSheaf
end LoF
end HeytingLean
