import HeytingLean.CCI.Core
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.FraudProofToy
import HeytingLean.Crypto.ZK.BridgeToy
import HeytingLean.Crypto.ZK.RangeProofExample
import HeytingLean.Crypto.ZK.PrivateVotingExample
import HeytingLean.Crypto.ZK.AnonymousCredentialsExample
import HeytingLean.Blockchain.Rollup.Model

/-
# Crypto.ZK.Spec

Identifiers and metadata for zero-knowledge proof system properties and
applications (section 4 and selected bridge rows).
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec

universe u

open HeytingLean.CCI
open HeytingLean.LoF
open HeytingLean.Blockchain

inductive PropertyId
  -- 4.1 SNARK systems
  | groth16Soundness
  | plonkSoundness
  | halo2Correctness
  | r1csSatisfiability
  | circuitCompilationCorrectness
  -- 4.2 STARK systems
  | friProtocolCorrectness
  | airConstraintsCorrectness
  | starkSoundness
  | cairoExecutionCorrectness
  -- 4.3 ZK applications
  | zkRollupStateTransition
  | zkEvmEquivalence
  | privateVotingCorrectness
  | anonymousCredentialsCorrectness
  | rangeProofsCorrectness
  -- Bridge-related ZK properties
  | fraudProofValidity
  | zkBridgeSoundness
  deriving DecidableEq, Repr

def PropertyId.slug : PropertyId → String
  | .groth16Soundness           => "zk.snark.groth16_soundness"
  | .plonkSoundness             => "zk.snark.plonk_soundness"
  | .halo2Correctness           => "zk.snark.halo2_correctness"
  | .r1csSatisfiability         => "zk.r1cs.satisfiability"
  | .circuitCompilationCorrectness => "zk.r1cs.circuit_compilation_correctness"
  | .friProtocolCorrectness     => "zk.stark.fri_protocol_correctness"
  | .airConstraintsCorrectness  => "zk.stark.air_constraints_correctness"
  | .starkSoundness             => "zk.stark.soundness"
  | .cairoExecutionCorrectness  => "zk.stark.cairo_execution_correctness"
  | .zkRollupStateTransition    => "zk.app.zkrollup_state_transition"
  | .zkEvmEquivalence           => "zk.app.zkevm_equivalence"
  | .privateVotingCorrectness   => "zk.app.private_voting"
  | .anonymousCredentialsCorrectness => "zk.app.anonymous_credentials"
  | .rangeProofsCorrectness     => "zk.app.range_proofs"
  | .fraudProofValidity         => "bridge.fraud_proof_validity"
  | .zkBridgeSoundness          => "bridge.zk_bridge_soundness"

def PropertyId.title : PropertyId → String
  | .groth16Soundness           => "Groth16 Soundness"
  | .plonkSoundness             => "PLONK Soundness"
  | .halo2Correctness           => "Halo2 Correctness"
  | .r1csSatisfiability         => "R1CS Satisfiability"
  | .circuitCompilationCorrectness => "Circuit Compilation"
  | .friProtocolCorrectness     => "FRI Protocol"
  | .airConstraintsCorrectness  => "AIR Constraints"
  | .starkSoundness             => "STARK Soundness"
  | .cairoExecutionCorrectness  => "Cairo Execution"
  | .zkRollupStateTransition    => "zkRollup State Transition"
  | .zkEvmEquivalence           => "zkEVM Equivalence"
  | .privateVotingCorrectness   => "Private Voting"
  | .anonymousCredentialsCorrectness => "Anonymous Credentials"
  | .rangeProofsCorrectness     => "Range Proofs"
  | .fraudProofValidity         => "Fraud Proof Validity"
  | .zkBridgeSoundness          => "ZK Bridge Soundness"

def PropertyId.description : PropertyId → String
  | .groth16Soundness =>
      "Groth16 SNARK is sound: accepted proofs correspond to valid witnesses."
  | .plonkSoundness =>
      "PLONK-style universal SNARKs are sound under their algebraic assumptions."
  | .halo2Correctness =>
      "Halo2 recursive proof system composes proofs without breaking soundness."
  | .r1csSatisfiability =>
      "R1CS semantics correctly capture constraint system satisfiability."
  | .circuitCompilationCorrectness =>
      "High-level programs compile to R1CS circuits preserving semantics."
  | .friProtocolCorrectness =>
      "FRI provides correct low-degree testing for polynomial oracles."
  | .airConstraintsCorrectness =>
      "AIR encodings faithfully represent transition relations over traces."
  | .starkSoundness =>
      "STARK protocols are sound given FRI and hash/commitment assumptions."
  | .cairoExecutionCorrectness =>
      "Cairo execution traces correspond to valid VM semantics."
  | .zkRollupStateTransition =>
      "zkRollup state transition proofs are sound with respect to the rollup spec."
  | .zkEvmEquivalence =>
      "zkEVM execution matches EVM semantics for all programs."
  | .privateVotingCorrectness =>
      "ZK-based private voting preserves ballot privacy and verifiability."
  | .anonymousCredentialsCorrectness =>
      "Anonymous credential schemes prove attributes without revealing identity."
  | .rangeProofsCorrectness =>
      "Range proofs demonstrate bounds on values without revealing them."
  | .fraudProofValidity =>
      "Optimistic bridge fraud proofs correctly detect invalid state transitions."
  | .zkBridgeSoundness =>
      "ZK-based bridges are sound: accepted proofs correspond to valid messages."

def PropertyId.toExpr (p : PropertyId) : Expr :=
  Expr.atom p.slug

/-- Specification-level statement for the optimistic-bridge fraud-proof
    validity row (`fraudProofValidity`), instantiated by the example model
    `FraudProofToy`. -/
def FraudProofValidityStatement : Prop :=
  FraudProofToy.Statement

/-- `FraudProofValidityStatement` holds, witnessed directly by
    `FraudProofToy.statement_holds`. -/
theorem fraudProofValidityStatement_holds :
    FraudProofValidityStatement :=
  FraudProofToy.statement_holds

/-- Specification-level statement for the ZK bridge soundness row
    (`zkBridgeSoundness`), instantiated by the example model `BridgeToy`. -/
def ZKBridgeSoundnessStatement : Prop :=
  BridgeToy.Statement

/-- `ZKBridgeSoundnessStatement` holds, witnessed directly by
    `BridgeToy.statement_holds`. -/
theorem zkBridgeSoundnessStatement_holds :
    ZKBridgeSoundnessStatement :=
  BridgeToy.statement_holds

/-- Specification-level statement for the range-proofs correctness row
    (`rangeProofsCorrectness`), instantiated by the example model
    `RangeProofExample`. At this level we take "correctness" to mean both
    soundness and completeness of the example verifier, together with a
    `Form`/Bool-lens realisation of the range predicate. -/
def RangeProofsFormStatement : Prop :=
  ∀ p : RangeProofExample.Proof,
    RangeProofExample.verify p =
      BoolLens.eval RangeProofExample.rangeForm (RangeProofExample.envOf p)

/-- `RangeProofsFormStatement` holds: the example verifier coincides with
    the `Form`-level evaluation of `rangeForm` under `envOf`. -/
theorem rangeProofsFormStatement_holds :
    RangeProofsFormStatement := by
  intro p
  simpa using RangeProofExample.verify_eq_eval_rangeForm p

/-- Combined correctness statement for the range-proofs row:
    soundness and completeness of the example verifier, plus the fact that
    it is realised by the `Form`/Bool-lens predicate `rangeForm`/`envOf`. -/
def RangeProofsCorrectnessStatement : Prop :=
  RangeProofExample.SoundnessStatement ∧
    RangeProofExample.CompletenessStatement ∧
      RangeProofsFormStatement

/-- `RangeProofsCorrectnessStatement` holds, witnessed by the
    soundness/completeness theorems for the example verifier and the
    `Form`-level characterisation. -/
theorem rangeProofsCorrectnessStatement_holds :
    RangeProofsCorrectnessStatement :=
  And.intro
    RangeProofExample.soundnessStatement_holds
    (And.intro
      RangeProofExample.completenessStatement_holds
      rangeProofsFormStatement_holds)

/-- Specification-level statement for the private-voting correctness
    row (`privateVotingCorrectness`), instantiated by the example model
    `PrivateVotingExample`. -/
def PrivateVotingCorrectnessStatement : Prop :=
  PrivateVotingExample.Statement

/-- `PrivateVotingCorrectnessStatement` holds, witnessed directly by
    `PrivateVotingExample.statement_holds`. -/
theorem privateVotingCorrectnessStatement_holds :
    PrivateVotingCorrectnessStatement :=
  PrivateVotingExample.statement_holds

/-- Specification-level statement for the anonymous-credentials
    correctness row (`anonymousCredentialsCorrectness`), instantiated
    by the example model `AnonymousCredentialsExample`. At this level we
    bundle attribute-correctness (accepted proofs correspond to issued
    credentials) and anonymity (the verifier's decision is independent
    of the holder identity). -/
def AnonymousCredentialsCorrectnessStatement : Prop :=
  AnonymousCredentialsExample.Statement

/-- `AnonymousCredentialsCorrectnessStatement` holds, witnessed
    directly by the example anonymous-credentials model. -/
theorem anonymousCredentialsCorrectnessStatement_holds :
    AnonymousCredentialsCorrectnessStatement :=
  AnonymousCredentialsExample.statement_holds

/-- Specification-level statement for the zkRollup state-transition row
    (`zkRollupStateTransition`), instantiated by the concrete Ωᵣ-level
    rollup spec `Rollup.specForTxs`.

For any choice of underlying Heyting algebra `α` with reentry nucleus
`R` and any transaction list `txs`, the Ωᵣ-level rollup spec
`specForTxs (R := R) txs` admits a core-valid single step that realises
the concrete `applyTxs`/`updateCommit` transition. This is expressed via
the bundled `RollupStepValidStatement`. -/
def ZKRollupStateTransitionStatement : Prop :=
  ∀ {α : Type u} [PrimaryAlgebra α] (R : Reentry α)
    (txs : List Rollup.Tx),
    Rollup.RollupStepValidStatement (R := R) (n := 1)
      (spec := Rollup.specForTxs (R := R) txs)
      (encode := id)
      (decode := id)
      (txs := txs)

/-- `ZKRollupStateTransitionStatement` holds, witnessed directly by the
    concrete rollup single-step correctness theorem
    `Rollup.rollupStepValid_concrete`. -/
theorem zkRollupStateTransitionStatement_holds :
    ZKRollupStateTransitionStatement := by
  intro α _ R txs
  simpa using
    (Rollup.rollupStepValid_concrete (R := R) (txs := txs))

end Spec
end ZK
end Crypto
end HeytingLean
