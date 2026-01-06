import HeytingLean.Basic
import HeytingLean.Governance.Model

/-
# Crypto.ZK.PrivateVotingExample

Minimal example model backing the `privateVotingCorrectness` ZK property.

This model abstracts away cryptographic details and focuses on the
shape of a ZK proof for tally correctness: whenever the verifier
accepts a proof, the published tally is equal to the true tally
computed from the underlying ballots.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace PrivateVotingExample

open HeytingLean.Governance
open HeytingLean.Governance.Model

/-- Example ZK proof for private-voting correctness: carries a list of
    ballots and a claimed tally. In a real system this would also carry
    commitments and a proof; here we model only the semantic payload. -/
structure Proof where
  ballots : List Ballot
  tally   : Tally
  deriving Repr

/-- Example verifier: accepts exactly when the claimed tally is the result
    of `tallyBallots` on the underlying ballots. -/
def verify (p : Proof) : Bool :=
  if tallyBallots p.ballots = p.tally then true else false

/-- Bundled correctness statement: if `verify` accepts, then the tally
    equals `tallyBallots` on the underlying ballots. -/
def Statement : Prop :=
  ∀ p : Proof, verify p = true → tallyBallots p.ballots = p.tally

/-- `Statement` holds by unfolding `verify` and analysing the `if`. -/
theorem statement_holds : Statement := by
  intro p hAccept
  unfold verify at hAccept
  by_cases hEq : tallyBallots p.ballots = p.tally
  · -- In the equal case, we can simply return `hEq`.
    exact hEq
  · -- In the unequal case, the verifier reduces to `false`,
    -- contradicting `hAccept`.
    have : False := by
      have hAccept' := hAccept
      simp [hEq] at hAccept'
    exact False.elim this

end PrivateVotingExample
end ZK
end Crypto
end HeytingLean
