import Lean
import Lean.Data.Json
import HeytingLean.Crypto.CoreTypes
import HeytingLean.Crypto.Hash.Poseidon

/-!
Deterministic proof-token model for BN254/Groth16-style integration.

This module intentionally models the *shape* of a SNARK interface while
remaining executable and auditable: `proveStructureEvalTrace` produces a
domain-separated commitment token, and `verifyStructureEvalTrace` checks it
by recomputation.  This is not a zero-knowledge proof; it is a stable
integration boundary until an actual prover/verifier is wired in.
-/

namespace HeytingLean
namespace Crypto
namespace ZK

open Lean
open HeytingLean.Crypto

structure Params where
  curve : String := "BN254"
  scheme : String := "Groth16"
  deriving Repr

def setupParams : Params := {}

abbrev Proof := String

def proveStructureEvalTrace (formJson : Json)
    (w : Crypto.WitnessCore)
    (p : Crypto.PublicInputsCore) : Except String Proof :=
  if !p.isValid then
    .error "invalid public inputs"
  else if !w.isSane then
    .error "invalid witness"
  else
    let formC_new := Crypto.Hash.commitForm formJson.compress
    let formC_legacy := HeytingLean.Crypto.commitString "FORM" formJson.compress
    let formC := if p.form_commitment == formC_new then formC_new else formC_legacy
    if formC ≠ p.form_commitment then
      .error "form commitment mismatch"
    else
      let tag := s!"{formC}:{p.initial_state}:{p.final_state}:{p.lens_selector}"
      .ok (Crypto.Hash.poseidonCommit "PROOF" tag)

def verifyStructureEvalTrace (formJson : Json)
    (p : Crypto.PublicInputsCore)
    (π : Proof) : Bool :=
  if !p.isValid then
    false
  else
    let formC_new := Crypto.Hash.commitForm formJson.compress
    let formC_legacy := HeytingLean.Crypto.commitString "FORM" formJson.compress
    let formC := if p.form_commitment == formC_new then formC_new else formC_legacy
    if formC ≠ p.form_commitment then false
    else
      let tag := s!"{formC}:{p.initial_state}:{p.final_state}:{p.lens_selector}"
      let expected := Crypto.Hash.poseidonCommit "PROOF" tag
      expected == π

end ZK
end Crypto
end HeytingLean
