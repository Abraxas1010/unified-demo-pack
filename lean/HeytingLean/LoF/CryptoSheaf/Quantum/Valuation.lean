import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Real.Basic

universe u

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum

/-- A simple valuation on a Heyting algebra: monotone + submodular + normalized.

Note: concrete instances are added in example modules to keep the core minimal.
-/
structure Valuation (α : Type u) [HeytingAlgebra α] where
  v : α → ℝ
  mono : ∀ {x y : α}, x ≤ y → v x ≤ v y
  submod : ∀ (x y : α), v (x ⊓ y) + v (x ⊔ y) ≤ v x + v y
  norm_top : v (⊤ : α) = 1
  norm_bot : v (⊥ : α) = 0

end Quantum
end CryptoSheaf
end LoF
end HeytingLean
