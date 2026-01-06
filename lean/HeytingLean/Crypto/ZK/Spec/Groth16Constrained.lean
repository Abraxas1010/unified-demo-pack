import HeytingLean.Crypto.ZK.Spec.Groth16

/-!
# Crypto.ZK.Spec.Groth16Constrained

Protocol-level *shape* for "multiple constraints + public/private separation"
on top of the current Groth16 verifier/prover pair.

This does **not** claim real Groth16/R1CS soundness yet. Instead it:

* models a constraint system as a list of predicates `Constraint` over
  public inputs and witness;
* defines what it means for a witness to satisfy a list of constraints; and
* packages a "knowledge soundness" statement: under an explicit
  extractability assumption (plus an additional assumption that the prover
  only outputs proofs for constraint-satisfying witnesses), verifier acceptance
  implies existence of a sane, constraint-satisfying witness explaining the proof.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Groth16Constrained

open HeytingLean.Crypto.ZK
open HeytingLean.Crypto.ZK.Spec.Groth16

/-- A constraint relating public inputs to a (private) witness. -/
abbrev Constraint := PublicInputsCore → WitnessCore → Prop

/-- A witness satisfies a list of constraints iff it satisfies each constraint in the list. -/
def Satisfies (cs : List Constraint) (p : PublicInputsCore) (w : WitnessCore) : Prop :=
  ∀ c ∈ cs, c p w

/-- A constrained Groth16 instance: a base `Instance` plus a (finite) list of constraints
that are intended to be enforced by the circuit/statement being proved. -/
structure ConstrainedInstance where
  base : Groth16.Instance
  constraints : List Constraint

namespace ConstrainedInstance

abbrev formJson (inst : ConstrainedInstance) : Lean.Json := inst.base.pub.formJson
abbrev pubInputs (inst : ConstrainedInstance) : PublicInputsCore := inst.base.pub.pub

end ConstrainedInstance

/-- Additional assumption tying the prover to constraints:
whenever the prover outputs `.ok π`, the provided witness satisfies the constraints. -/
def ProverRespectsConstraints : Prop :=
  ∀ (formJson : Lean.Json) (p : PublicInputsCore) (cs : List Constraint)
    (w : WitnessCore) (π : Proof),
      proveStructureEvalTrace formJson w p = .ok π →
        Satisfies cs p w

namespace Stub

/-- Two verifier-aligned constraints showcasing public/private separation:

* a **public** constraint requiring `PublicRel formJson p`;
* a **private** constraint requiring `w.isSane = true`.

These are precisely the conditions enforced (directly or indirectly) by the
current prover/verifier pair.
-/
def publicPrivateConstraints (formJson : Lean.Json) : List Constraint :=
  [ (fun p _w => PublicRel formJson p)
  , (fun _p w => w.isSane = true) ]

private theorem satisfies_publicPrivateConstraints_of_prove_ok
    (formJson : Lean.Json) (p : PublicInputsCore) (w : WitnessCore) (π : Proof)
    (hOk : proveStructureEvalTrace formJson w p = .ok π) :
    Satisfies (publicPrivateConstraints formJson) p w := by
  intro c hc
  -- Only two constraints; dispatch by list membership.
  rcases List.mem_cons.1 hc with h0 | hc'
  · -- PublicRel constraint.
    subst h0
    exact Groth16.publicRel_of_prove_ok (formJson := formJson) (p := p) (w := w) (π := π) hOk
  · rcases List.mem_cons.1 hc' with h1 | hc''
    · -- isSane constraint (provable from the successful prover run).
      subst h1
      cases hSane : w.isSane with
      | false =>
          have : False := by
            cases hValid : p.isValid <;>
              simp [proveStructureEvalTrace, hValid, hSane] at hOk
          cases this
      | true =>
          rfl
    · cases hc''

/-- Protocol instance for constrained Groth16 soundness (knowledge soundness shape):

Assumptions:
* `ExtractionAssumption`: accepted proofs are witness-extractable (w.r.t. the prover)
* `ProverRespectsConstraints`: any witness producing a proof satisfies the constraints

Statement:
* public inputs satisfy `PublicRel`, and
* there exists a sane witness `w` explaining the accepted proof and satisfying all constraints.
-/
def constrainedKnowledgeProtocol :
    Groth16.Protocol (Inst := ConstrainedInstance) :=
  { assumptions := ExtractionAssumption ∧ ProverRespectsConstraints
    Proof := Proof
    Statement := fun inst π =>
      PublicRel inst.formJson inst.pubInputs ∧
        ∃ w : WitnessCore,
          w.isSane = true ∧
          proveStructureEvalTrace inst.formJson w inst.pubInputs = .ok π ∧
          Satisfies inst.constraints inst.pubInputs w
    verify := fun inst π =>
      verifyStructureEvalTrace inst.formJson inst.pubInputs π
    sound := by
      intro hAssump inst π hVerify
      rcases hAssump with ⟨hExtract, hProver⟩
      have hPR :
          PublicRel inst.formJson inst.pubInputs ∧
            WitnessExtractable inst.formJson inst.pubInputs π :=
        publicRel_and_witnessExtractable_of_verify_true hExtract
          (formJson := inst.formJson) (p := inst.pubInputs) (π := π) hVerify
      rcases hPR with ⟨hPublicRel, hWE⟩
      rcases hWE with ⟨w, hSane, hProveOk⟩
      have hSat : Satisfies inst.constraints inst.pubInputs w :=
        hProver inst.formJson inst.pubInputs inst.constraints w π hProveOk
      refine ⟨hPublicRel, ⟨w, hSane, hProveOk, hSat⟩⟩ }

/-- Bundled protocol-level soundness statement for `constrainedKnowledgeProtocol`. -/
theorem constrainedKnowledgeProtocol_soundness :
    Groth16.ProtocolSoundnessStatement constrainedKnowledgeProtocol :=
  Groth16.protocolSoundnessStatement_holds constrainedKnowledgeProtocol

/-! ### Specialization: verifier-enforced public/private constraints

This is a concrete "multiple constraints" theorem that does not assume an
arbitrary `ProverRespectsConstraints`: it uses the fixed constraint list
`publicPrivateConstraints` that is already implied by a successful prover run.
-/

/-- A constrained instance using `publicPrivateConstraints formJson`. -/
def publicPrivateInstance (base : Groth16.Instance) : ConstrainedInstance :=
  { base := base, constraints := publicPrivateConstraints base.pub.formJson }

/-- Under `ExtractionAssumption`, verifier acceptance implies existence of a sane
    witness explaining the proof and satisfying the verifier-aligned public/private
    constraints. -/
theorem publicPrivateProtocol_soundness (hA : ExtractionAssumption) :
    ∀ (base : Groth16.Instance) (π : Proof),
      verifyStructureEvalTrace base.pub.formJson base.pub.pub π = true →
        ∃ w : WitnessCore,
          w.isSane = true ∧
          proveStructureEvalTrace base.pub.formJson w base.pub.pub = .ok π ∧
          Satisfies (publicPrivateConstraints base.pub.formJson) base.pub.pub w := by
  intro base π hVerify
  -- Extract witness from acceptance using the explicit assumption.
  have hWE : WitnessExtractable base.pub.formJson base.pub.pub π :=
    hA base.pub.formJson base.pub.pub π hVerify
  rcases hWE with ⟨w, hSane, hOk⟩
  refine ⟨w, hSane, hOk, ?_⟩
  exact satisfies_publicPrivateConstraints_of_prove_ok
    (formJson := base.pub.formJson) (p := base.pub.pub) (w := w) (π := π) hOk

end Stub

end Groth16Constrained
end Spec
end ZK
end Crypto
end HeytingLean
