import HeytingLean.Crypto.ZK.Spec.Groth16
import Mathlib.Data.Bool.Basic

/-!
# Minimal Groth16 protocol skeleton and soundness test

We instantiate the abstract `Spec.Groth16.Protocol` with the existing
verifier `verifyStructureEvalTrace`. The statement captured is the
only guarantee the current verifier enforces: public inputs passed the local
`isValid` check. This keeps the test aligned with the current implementation
while remaining proof-hole-free and axiom-auditable.
-/

open HeytingLean.Crypto.ZK.Spec.Groth16
open HeytingLean.Crypto
open HeytingLean.Crypto.ZK

/-- Helper: commitment choice mirroring the verifier (new/legacy). -/
def expectedCommit (formJson : Lean.Json) (p : PublicInputsCore) : String :=
  let formC_new := HeytingLean.Crypto.Hash.commitForm formJson.compress
  let formC_legacy := HeytingLean.Crypto.commitString "FORM" formJson.compress
  if p.form_commitment == formC_new then formC_new else formC_legacy

/-- Minimal protocol instance using the verifier; statement is the
    local validity check on public inputs. -/
def minimalGroth16Protocol : Protocol :=
  { assumptions := True
    Proof := Proof
    Statement := fun inst _ => PublicRel inst.pub.formJson inst.pub.pub
    verify := fun inst π => verifyStructureEvalTrace inst.pub.formJson inst.pub.pub π
    sound := by
      intro _ inst π h
      exact publicRel_of_verify_true (formJson := inst.pub.formJson) (p := inst.pub.pub) (π := π) h }

/-- Example concrete instance compatible with the verifier. -/
def minimalForm : Lean.Json := Lean.Json.null

def minimalPub : PublicInputsCore :=
  { form_commitment := expectedCommit minimalForm
      { form_commitment := "", initial_state := "", final_state := "", lens_selector := 0 }
    , initial_state := "init"
    , final_state := "final"
    , lens_selector := 0 }

def minimalWit : WitnessCore :=
  { reentry_values := []
  , boundary_marks := []
  , eval_trace := [] }

def minimalInst : Instance :=
  { params := ZK.setupParams
    , pub := { formJson := minimalForm, pub := minimalPub }
    , wit := minimalWit }

/-- Protocol-level soundness for the minimal verifier-aligned protocol. -/
theorem minimalGroth16_soundness :
    ProtocolSoundnessStatement minimalGroth16Protocol :=
  protocolSoundnessStatement_holds _

-- QA: axiom audit.
#print axioms minimalGroth16_soundness

-- Sanity eval: verifier on the concrete instance using the prover output.
#eval verifyStructureEvalTrace minimalForm minimalPub
  (HeytingLean.Crypto.Hash.poseidonCommit "PROOF"
    s!"{expectedCommit minimalForm minimalPub}:{minimalPub.initial_state}:{minimalPub.final_state}:{minimalPub.lens_selector}")
