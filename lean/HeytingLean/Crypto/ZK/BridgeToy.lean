import HeytingLean.Basic

/-
# Crypto.ZK.BridgeToy

Minimal example model backing the `zkBridgeSoundness` ZK property. It
abstracts away concrete cryptographic details and focuses on the shape
of a sound verifier: whenever a proof is accepted, the claimed message
equality actually holds.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace BridgeToy

/-- Example bridge proof containing a source and destination message and a
    “claimed equality” between them. -/
structure Proof where
  srcMsg : Nat
  dstMsg : Nat
  deriving Repr, DecidableEq

/-- Example verifier: accepts exactly when the two messages are equal. -/
def verify (p : Proof) : Bool :=
  if p.srcMsg = p.dstMsg then true else false

/-- Bundled soundness statement: whenever `verify` accepts a proof, the
    source and destination messages are equal. -/
def Statement : Prop :=
  ∀ p : Proof, verify p = true → p.srcMsg = p.dstMsg

/-- `Statement` holds by case analysis on the `if` in `verify`. -/
theorem statement_holds : Statement := by
  intro p hAccept
  unfold verify at hAccept
  by_cases hEq : p.srcMsg = p.dstMsg
  · -- In the equal case, the verifier reduces to `true`.
    simp [hEq] at hAccept
    exact hEq
  · -- In the unequal case, the verifier reduces to `false`, contradicting `hAccept`.
    simp [hEq] at hAccept

end BridgeToy
end ZK
end Crypto
end HeytingLean
