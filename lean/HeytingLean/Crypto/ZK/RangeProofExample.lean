import HeytingLean.Basic
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens

/-
# Crypto.ZK.RangeProofExample

Minimal example model backing the `rangeProofsCorrectness` ZK property. It
captures the intended shape of a range proof: if a verifier accepts, the
underlying value lies within the claimed bounds.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace RangeProofExample

/-- Example range-proof record with a value and inclusive lower/upper bounds. -/
structure Proof where
  val : Int
  lo  : Int
  hi  : Int
  deriving Repr, DecidableEq

/-- Example verifier: accepts exactly when `lo ≤ val ≤ hi`. -/
def verify (p : Proof) : Bool :=
  if p.lo ≤ p.val ∧ p.val ≤ p.hi then true else false

/-- Boolean environment for the one-variable range form. -/
abbrev Env1 := Crypto.BoolLens.Env 1

/-- `Form`-level encoding of the range predicate as a single atom
    whose truth value is given by `verify`. -/
def rangeForm : Crypto.Form 1 :=
  Crypto.Form.var ⟨0, by decide⟩

/-- Environment feeding the verifier's decision into the atomic
    variable used by `rangeForm`. -/
def envOf (p : Proof) : Env1 :=
  fun _ => verify p

/-- Evaluating `rangeForm` under `envOf p` reproduces the verifier's
    boolean decision. -/
lemma eval_rangeForm (p : Proof) :
    BoolLens.eval rangeForm (envOf p) = verify p := by
  unfold rangeForm envOf
  simp [BoolLens.eval]

/-- The example verifier `verify` coincides with the `Form`/Bool-lens
    evaluation of `rangeForm` under `envOf`. -/
lemma verify_eq_eval_rangeForm (p : Proof) :
    verify p = BoolLens.eval rangeForm (envOf p) := by
  simp [eval_rangeForm p]

/-- Soundness statement: if `verify` accepts, then `val` lies within
    the claimed range `[lo, hi]`. -/
def SoundnessStatement : Prop :=
  ∀ p : Proof, verify p = true → p.lo ≤ p.val ∧ p.val ≤ p.hi

/-- `SoundnessStatement` holds by unfolding `verify` and analysing the
    `if`. -/
theorem soundnessStatement_holds : SoundnessStatement := by
  intro p hAccept
  unfold verify at hAccept
  by_cases hRange : p.lo ≤ p.val ∧ p.val ≤ p.hi
  · -- In the in-range case, the verifier reduces to `true`.
    simp [hRange] at hAccept
    exact hRange
  · -- In the out-of-range case, the verifier reduces to `false`,
    -- contradicting `hAccept`.
    simp [hRange] at hAccept

/-- Convenience lemma matching the CLI/test API: accepted proofs imply the range property. -/
theorem statement_holds (p : Proof) (hAccept : verify p = true) : p.lo ≤ p.val ∧ p.val ≤ p.hi :=
  soundnessStatement_holds p hAccept

/-- Completeness statement: if a value lies in the range `[lo, hi]`,
    then the canonical proof record with these fields is accepted by
    `verify`. -/
def CompletenessStatement : Prop :=
  ∀ (val lo hi : Int),
    lo ≤ val ∧ val ≤ hi →
      verify { val := val, lo := lo, hi := hi } = true

/-- `CompletenessStatement` holds by unfolding `verify` and supplying
    the range witness to the `if`. -/
theorem completenessStatement_holds : CompletenessStatement := by
  intro val lo hi hRange
  unfold verify
  -- In this case the `if` branch is taken.
  simp [hRange]

end RangeProofExample
end ZK
end Crypto
end HeytingLean
