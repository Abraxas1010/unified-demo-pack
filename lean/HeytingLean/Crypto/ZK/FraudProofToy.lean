import HeytingLean.Basic

/-
# Crypto.ZK.FraudProofToy

Minimal example statement backing the `fraudProofValidity` ZK property. It
abstracts away the concrete bridge model and focuses on the arithmetic
shape of a fraud proof: if a posted `after` state differs from `before`
by a positive amount, then it cannot equal `before`.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace FraudProofToy

/-- Bundled fraud-proof validity statement in example form. -/
def Statement : Prop :=
  ∀ (before after w : Nat),
    after = before + Nat.succ w → after ≠ before

/-- `Statement` holds by a simple arithmetic contradiction. -/
theorem statement_holds : Statement := by
  intro before after w hEq
  intro hEq'
  have hgt : before < after := by
    rw [hEq]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos w)
  have hgt' := hgt
  simp [hEq'] at hgt'

end FraudProofToy
end ZK
end Crypto
end HeytingLean
