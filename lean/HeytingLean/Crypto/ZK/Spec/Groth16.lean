import Lean
import Lean.Data.Json
import Mathlib.Logic.Basic
import HeytingLean.Crypto.CoreTypes
import HeytingLean.Crypto.ZK.Groth16

/-
# Crypto.ZK.Spec.Groth16

Specification façade for the Groth16-style `StructureEvalTrace` implementation.

This module does not fix a full cryptographic Groth16 semantics yet.
Instead it provides two layers:

* an **implementation-level façade**:
  - packages the public inputs and witness into a small `Instance` record;
  - defines a spec-level relation `Rel` describing when an instance is
    considered well-formed with respect to the current prover/verifier; and
  - proves completeness and soundness properties that exactly
    capture what the current prover/verifier pair enforce; and
* a **protocol-level skeleton**:
  - an abstract `Protocol` interface with an explicit `Assumptions` field;
  - a bundled `ProtocolSoundnessStatement` that reuses the `sound` field.

The second layer is where genuine Groth16 soundness theorems under
explicit cryptographic assumptions are intended to live: concrete
developments are expected to instantiate `Protocol` and justify its
`sound` field from pairing / knowledge-of-exponent / hash assumptions.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Groth16

open Lean
open HeytingLean.Crypto
open HeytingLean.Crypto.ZK

/-- Public description of a Groth16 instance: form JSON and public inputs. -/
structure Public where
  formJson : Json
  pub      : PublicInputsCore

/-- Full Groth16 instance, including witness. -/
structure Instance where
  params : Params
  pub    : Public
  wit    : WitnessCore

/-- Spec-level relation tying together the sanity conditions on public
    inputs and witness with the expected form commitment. This is the
    current stand-in for the intended Ωᵣ / `Form` relation
    that will ultimately connect `formJson` to core semantics. -/
def Rel (inst : Instance) : Prop :=
  inst.pub.pub.isValid = true ∧
  inst.wit.isSane = true ∧
  inst.pub.pub.form_commitment =
    Crypto.Hash.commitForm inst.pub.formJson.compress

/-- Bridge from propositional equality on strings to boolean equality
    for the built-in `BEq String` instance, following the same pattern
    as the Merkle-model lemma. -/
lemma string_eq_imp_beq (s₁ s₂ : String) (h : s₁ = s₂) :
    (s₁ == s₂) = true := by
  classical
  -- Rewrite `==` to `decide (s₁ = s₂)` using the `LawfulBEq` machinery.
  have hbeq : (s₁ == s₂) = decide (s₁ = s₂) := by
    simp [beq_eq_decide]
  -- Turn propositional equality into a `decide = true` fact.
  have hdec : decide (s₁ = s₂) = true :=
    (decide_eq_true_eq (p := s₁ = s₂)).symm ▸ h
  -- Combine the two equalities.
  simp [hbeq, hdec]

/-- Implementation-level completeness for the current Groth16-style interface:

If an instance satisfies `Rel` (public inputs valid, witness sane, and
the published form commitment matches the hash
`commitForm formJson.compress` used by the prover/verifier), then the prover
succeeds and the resulting proof is accepted by the verifier. This ties
`proveStructureEvalTrace` and `verifyStructureEvalTrace` for well-formed
inputs, without making any cryptographic assumptions. -/
def CompletenessStatement : Prop :=
  ∀ (inst : Instance),
    Rel inst →
    ∃ π : Proof,
      proveStructureEvalTrace inst.pub.formJson
          inst.wit inst.pub.pub = .ok π ∧
        verifyStructureEvalTrace inst.pub.formJson
          inst.pub.pub π = true

/-- `CompletenessStatement` holds for the current Groth16 interface: under
    the stated well-formedness and commitment conditions, the prover’s
    output is always accepted by the verifier. -/
theorem completenessStatement_holds :
    CompletenessStatement := by
  intro inst hRel
  classical
  rcases hRel with ⟨hValid, hSane, hCommit⟩
  -- Abbreviations matching the prover/verifier arguments.
  let formJson := inst.pub.formJson
  let p := inst.pub.pub
  let w := inst.wit
  -- Commitment hash used by the prover/verifier.
  let formC_new := Crypto.Hash.commitForm formJson.compress
  have hCommitNew : p.form_commitment = formC_new := by
    simpa [formJson, formC_new] using hCommit
  -- Prover output: simplify the definition under the hypotheses.
  have hProve :
      proveStructureEvalTrace formJson w p =
        .ok
          (Crypto.Hash.poseidonCommit "PROOF"
            s!"{formC_new}:{p.initial_state}:{p.final_state}:{p.lens_selector}") := by
    simp [proveStructureEvalTrace, formJson, p, w,
      hValid, hSane, formC_new, hCommitNew] at *
  -- Choose the prover’s proof as witness `π`.
  refine ⟨
    Crypto.Hash.poseidonCommit "PROOF"
      s!"{formC_new}:{p.initial_state}:{p.final_state}:{p.lens_selector}", ?_, ?_⟩
  · exact hProve
  · -- Verifier output: recomputes the same tag and commitment, so the
    -- equality check succeeds.
    have hVerify :
        verifyStructureEvalTrace formJson p
            (Crypto.Hash.poseidonCommit "PROOF"
              s!"{formC_new}:{p.initial_state}:{p.final_state}:{p.lens_selector}") =
          true := by
      have hValidBool : p.isValid = true := hValid
      -- Simplify the verifier with the same hypotheses as the prover.
      simp [verifyStructureEvalTrace, formJson, p,
        hValidBool, formC_new, hCommitNew] at *
    exact hVerify
/-- Soundness statement for the current Groth16-style
    interface: if the verifier accepts, then the public inputs pass the
    local validity check `isValid`.

This isolates what the current verifier actually enforces today. Deeper semantic
soundness (relating proofs to Ωᵣ / `Form` semantics and cryptographic
assumptions) is tracked separately in the plan. -/
def SoundnessStatement : Prop :=
  ∀ (formJson : Json) (p : PublicInputsCore) (π : Proof),
    verifyStructureEvalTrace formJson p π = true →
      p.isValid = true

/-- `SoundnessStatement` holds for the current Groth16 interface: whenever
    the verifier accepts, the initial public-input validity check must
    have succeeded. -/
theorem soundnessStatement_holds :
    SoundnessStatement := by
  intro formJson p π h
  -- Analyse the initial validity check in `verifyStructureEvalTrace`.
  cases hValid : p.isValid with
  | false =>
      -- If `p.isValid = false`, the verifier returns `false`, so it
      -- cannot be equal to `true`.
      have hFalse :
          verifyStructureEvalTrace formJson p π = false := by
        simp [verifyStructureEvalTrace, hValid]
      -- Contradiction with the hypothesis `h`.
      -- Combine `h` and `hFalse` to derive `false = true`.
      have hEq : false = true := by
        have hEq := h
        simp [hFalse] at hEq
      cases hEq
  | true =>
      -- In this branch `p.isValid = true`, which is exactly the goal.
      -- After rewriting by `hValid`, the goal reduces to `True`.
      rfl

/-! ## Stronger public-input soundness facts

The verifier checks both:

* `p.isValid = true`, and
* the published `form_commitment` matches either the "new" commitment
  `Crypto.Hash.commitForm formJson.compress` or a legacy commitment
  `Crypto.commitString "FORM" formJson.compress`.

The following proposition packages those public-input properties and a
corresponding soundness lemma extracts them from `verify = true`.
-/

/-- Public-input relation actually enforced by the verifier:
    validity plus a commitment match (new or legacy). -/
def PublicRel (formJson : Json) (p : PublicInputsCore) : Prop :=
  p.isValid = true ∧
    (p.form_commitment = Crypto.Hash.commitForm formJson.compress ∨
      p.form_commitment = HeytingLean.Crypto.commitString "FORM" formJson.compress)

/-- If the verifier accepts, then `PublicRel formJson p` holds. -/
theorem publicRel_of_verify_true :
    ∀ (formJson : Json) (p : PublicInputsCore) (π : Proof),
      verifyStructureEvalTrace formJson p π = true →
        PublicRel formJson p := by
  intro formJson p π h
  -- First, the `isValid` guard must have succeeded.
  have hValid : p.isValid = true := soundnessStatement_holds (formJson := formJson) (p := p) (π := π) h
  -- Now analyze which commitment branch the verifier took.
  classical
  let formC_new := Crypto.Hash.commitForm formJson.compress
  let formC_legacy := HeytingLean.Crypto.commitString "FORM" formJson.compress
  cases hBeq : (p.form_commitment == formC_new) with
  | false =>
      -- Verifier uses `formC_legacy` in this branch.
      have hCommit : p.form_commitment = formC_legacy := by
        have h' :
            (if formC_legacy ≠ p.form_commitment then false else
              let tag := s!"{formC_legacy}:{p.initial_state}:{p.final_state}:{p.lens_selector}"
              let expected := Crypto.Hash.poseidonCommit "PROOF" tag
              expected == π) = true := by
          simpa [verifyStructureEvalTrace, hValid, formC_new, formC_legacy, hBeq] using h
        by_cases hne : formC_legacy ≠ p.form_commitment
        · simp [hne] at h'
        · exact (not_ne_iff.mp hne).symm
      exact ⟨hValid, Or.inr hCommit⟩
  | true =>
      -- Verifier uses `formC_new` in this branch.
      have hCommit : p.form_commitment = formC_new := by
        have h' :
            (if formC_new ≠ p.form_commitment then false else
              let tag := s!"{formC_new}:{p.initial_state}:{p.final_state}:{p.lens_selector}"
              let expected := Crypto.Hash.poseidonCommit "PROOF" tag
              expected == π) = true := by
          simpa [verifyStructureEvalTrace, hValid, formC_new, formC_legacy, hBeq] using h
        by_cases hne : formC_new ≠ p.form_commitment
        · simp [hne] at h'
        · exact (not_ne_iff.mp hne).symm
      exact ⟨hValid, Or.inl hCommit⟩

/-! ## Prover-side facts

The prover rejects invalid public inputs, an insane witness, and a
form-commitment mismatch. The following lemma packages the corresponding
public-input relation extracted from a successful prover run.
-/

/-- If the prover returns `.ok π`, then the public inputs satisfy `PublicRel`. -/
theorem publicRel_of_prove_ok :
    ∀ (formJson : Json) (p : PublicInputsCore) (w : WitnessCore) (π : Proof),
      proveStructureEvalTrace formJson w p = .ok π →
        PublicRel formJson p := by
  intro formJson p w π hOk
  classical
  -- First, the prover's `isValid`/`isSane` guards must have passed.
  have hValid : p.isValid = true := by
    cases h' : p.isValid with
    | false =>
        have : False := by
          have hOk' := hOk
          simp [proveStructureEvalTrace, h'] at hOk'
        cases this
    | true =>
        rfl
  have hSane : w.isSane = true := by
    cases h' : w.isSane with
    | false =>
        have : False := by
          have hOk' := hOk
          simp [proveStructureEvalTrace, hValid, h'] at hOk'
        cases this
    | true =>
        rfl
  -- Now analyze the commitment branch (new/legacy).
  let formC_new := Crypto.Hash.commitForm formJson.compress
  let formC_legacy := HeytingLean.Crypto.commitString "FORM" formJson.compress
  cases hBeq : (p.form_commitment == formC_new) with
  | false =>
      -- In this branch the prover picks `formC_legacy` and checks it matches.
      have hCommit : p.form_commitment = formC_legacy := by
        have : (if formC_legacy ≠ p.form_commitment then Except.error "form commitment mismatch"
                else Except.ok (Crypto.Hash.poseidonCommit "PROOF"
                  s!"{formC_legacy}:{p.initial_state}:{p.final_state}:{p.lens_selector}")) = .ok π := by
          simpa [proveStructureEvalTrace, hValid, hSane, formC_new, formC_legacy, hBeq] using hOk
        by_cases hne : formC_legacy ≠ p.form_commitment
        · simp [hne] at this
        · exact (not_ne_iff.mp hne).symm
      exact ⟨hValid, Or.inr hCommit⟩
  | true =>
      -- In this branch the prover picks `formC_new` and checks it matches.
      have hCommit : p.form_commitment = formC_new := by
        have : (if formC_new ≠ p.form_commitment then Except.error "form commitment mismatch"
                else Except.ok (Crypto.Hash.poseidonCommit "PROOF"
                  s!"{formC_new}:{p.initial_state}:{p.final_state}:{p.lens_selector}")) = .ok π := by
          simpa [proveStructureEvalTrace, hValid, hSane, formC_new, formC_legacy, hBeq] using hOk
        by_cases hne : formC_new ≠ p.form_commitment
        · simp [hne] at this
        · exact (not_ne_iff.mp hne).symm
      exact ⟨hValid, Or.inl hCommit⟩

/-! ## Protocol-level assumption: extractability as an explicit assumption -/

/-- A proof `π` is witness-extractable w.r.t. `(formJson, p)` if there exists
    some witness `w` such that the prover would output exactly `π`. -/
def WitnessExtractable (formJson : Json) (p : PublicInputsCore) (π : Proof) : Prop :=
  ∃ w : WitnessCore, w.isSane = true ∧ proveStructureEvalTrace formJson w p = .ok π

/-- Explicit "knowledge/extractability" assumption for the Groth16 interface:
    whenever the verifier accepts, there exists a witness explaining the proof. -/
def ExtractionAssumption : Prop :=
  ∀ (formJson : Json) (p : PublicInputsCore) (π : Proof),
    verifyStructureEvalTrace formJson p π = true →
      WitnessExtractable formJson p π

/-- Under `ExtractionAssumption`, verifier acceptance implies both the public-input
    relation `PublicRel` and witness extractability. -/
theorem publicRel_and_witnessExtractable_of_verify_true (hA : ExtractionAssumption) :
    ∀ (formJson : Json) (p : PublicInputsCore) (π : Proof),
      verifyStructureEvalTrace formJson p π = true →
        PublicRel formJson p ∧ WitnessExtractable formJson p π := by
  intro formJson p π h
  refine ⟨publicRel_of_verify_true formJson p π h, ?_⟩
  exact hA formJson p π h

/-! ## Abstract Groth16 protocol interface

The following definitions provide a protocol-level skeleton for Groth16
soundness. They are intentionally abstract: concrete Groth16 instances
are expected to:

* fix a choice of `Assumptions` encoding the desired cryptographic
  hypotheses (knowledge-of-exponent, pairing non-degeneracy, hash
  binding, etc.);
* pick a type of proofs `Proof` and a statement predicate
  `Statement : Instance → Prop` (typically an Ωᵣ / `Form`-level relation);
* implement a Boolean verifier `verify : Instance → Proof → Bool`; and
* provide a `sound` field showing that under the assumptions, accepted
  proofs imply the intended statement.

At this level we do not commit to any particular choice of assumptions
or statement predicate: they are left as parameters of `Protocol`. -/

/-- Abstract Groth16 protocol over the current `Instance` type.

  * `assumptions` packages the cryptographic hypotheses under which
    soundness is claimed (e.g. knowledge-of-exponent, pairing
    assumptions, hash security). This is kept abstract so that concrete
    developments can spell out the exact shape they need (typically as a
    conjunction of named assumptions).
  * `Proof` is the type of proofs.
  * `Statement` is the semantic property that a Groth16 proof is
    intended to certify for a given instance (typically an Ωᵣ / `Form`
    relation, but left abstract here).
  * `verify` is the Boolean verifier for the protocol.
  * `sound` encodes protocol-level soundness: given the assumptions, any
    accepted proof certifies the intended statement. -/
structure Protocol (Inst : Type := Instance) where
  assumptions : Prop
  Proof       : Type
  Statement   : Inst → Proof → Prop
  verify      : Inst → Proof → Bool
  sound :
    assumptions →
      ∀ {inst : Inst} {π : Proof},
        verify inst π = true → Statement inst π

/-- Bundled protocol-level Groth16 soundness statement for a fixed
    protocol instance `P`: under its explicit assumptions, whenever the
    verifier accepts some instance/proof pair, the intended statement
    holds for that instance. -/
def ProtocolSoundnessStatement {Inst : Type} (P : Protocol (Inst := Inst)) : Prop :=
  P.assumptions →
    ∀ (inst : Inst) (π : P.Proof),
      P.verify inst π = true → P.Statement inst π

/-- `ProtocolSoundnessStatement P` holds for any abstract Groth16
    protocol instance `P`, by definition of its `sound` field. Concrete
    Groth16 arguments are meant to construct particular `P` together
    with an appropriate choice of assumptions. -/
theorem protocolSoundnessStatement_holds {Inst : Type} (P : Protocol (Inst := Inst)) :
    ProtocolSoundnessStatement P := by
  intro hAssump inst π h
  exact P.sound hAssump h

/-! ## Stub protocol-level soundness under explicit extractability

The `ExtractionAssumption` above is a protocol-level assumption: it says
accepted proofs are witness-extractable (knowledge soundness). Under that
assumption, the current verifier implies both:

* the public-input relation `PublicRel` actually enforced by the verifier; and
* existence of a sane witness `w` whose prover output equals the accepted proof.

We package this into a concrete `Protocol` instance so it can be exercised
by the same `ProtocolSoundnessStatement` harness as other systems.
-/

namespace Stub

/-- Protocol instance corresponding to the current verifier, with the
statement "accepted ⇒ public inputs satisfy `PublicRel` and the proof is
witness-extractable", under the explicit `ExtractionAssumption`. -/
def knowledgeProtocol : Protocol :=
  { assumptions := ExtractionAssumption
    Proof := Proof
    Statement := fun inst π =>
      PublicRel inst.pub.formJson inst.pub.pub ∧
        WitnessExtractable inst.pub.formJson inst.pub.pub π
    verify := fun inst π =>
      verifyStructureEvalTrace inst.pub.formJson inst.pub.pub π
    sound := by
      intro hA inst π h
      -- This is exactly the combined public-input + extractability lemma.
      simpa using
        (publicRel_and_witnessExtractable_of_verify_true hA
          (formJson := inst.pub.formJson) (p := inst.pub.pub) (π := π) h) }

/-- Protocol-level soundness statement for `knowledgeProtocol`. -/
theorem knowledgeProtocol_soundness :
    ProtocolSoundnessStatement knowledgeProtocol :=
  protocolSoundnessStatement_holds knowledgeProtocol

end Stub

end Groth16
end Spec
end ZK
end Crypto
end HeytingLean
