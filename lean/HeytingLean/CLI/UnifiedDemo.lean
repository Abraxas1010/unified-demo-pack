import HeytingLean.LoF.CryptoSheaf.Quantum.ContextualitySite
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel
import HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres
import HeytingLean.Crypto.FHE.NoiseHomomorphicSpec
import HeytingLean.Crypto.Lattice.NoiseMLWE
import HeytingLean.Crypto.ZK.SISPoKDemo
import HeytingLean.Quantum.QChannel
import HeytingLean.Quantum.Contextuality.MerminPeresRealization
import Lean.Data.Json

namespace HeytingLean
namespace CLI

open HeytingLean.LoF.CryptoSheaf.Quantum
open HeytingLean.Crypto
open HeytingLean.Crypto.FHE
open HeytingLean.Crypto.ZK
open HeytingLean.Quantum

-- Physical-process evidence (proof hooks only; keep runtime computable)
private def physicalPayload : String :=
  let ok : Bool :=
    Id.run do
      let Φ : HeytingLean.Quantum.KrausChannel 1 1 := HeytingLean.Quantum.KrausChannel.id 1
      let ρ : HeytingLean.Quantum.Mat 1 := 0
      let _ := Φ.trace_map (ρ := ρ)
      let _ := HeytingLean.Quantum.Contextuality.MerminPeres.row1_prod
      true
  "{\"qstate\":true,\"qchannel\":true,\"checks\":" ++ toString ok ++ "}"

-- Contextuality payload
private def contextualityPayload : String :=
  -- Keep this runtime-computable: the triangle demo cover has size 3.
  let coverSize : Nat := 3
  let ok : Bool :=
    Id.run do
      let _ := triangle_no_global
      let _ := HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres.no_assignment
      let _ := HeytingLean.Quantum.Contextuality.MerminPeres.row1_prod
      let _ := HeytingLean.Quantum.Contextuality.MerminPeres.col3_prod
      true
  "{\"contextual\":true," ++
    "\"cover_size\":" ++ toString coverSize ++ "," ++
    "\"witnesses\":{" ++
      "\"triangle\":{\"no_global\":true,\"kind\":\"possibilistic\"}," ++
      "\"mermin_peres\":{\"no_assignment\":true,\"quantum_realizable\":true}" ++
    "}," ++
    "\"checks\":" ++ toString ok ++ "}"

-- Valuation payload (cardinalities only)
private def valuationPayload : String :=
  -- Keep this runtime-computable (and schema-stable): the triangle witness supports are size 2.
  let sAB : Nat := 2
  let sBC : Nat := 2
  let sAC : Nat := 2
  let items :=
    "[{\"context\":\"ab\",\"size\":" ++ toString sAB ++ "}," ++
    "{\"context\":\"bc\",\"size\":" ++ toString sBC ++ "}," ++
    "{\"context\":\"ac\",\"size\":" ++ toString sAC ++ "}]"
  "{\"supports\":" ++ items ++ "}"

-- FHE smoke
namespace ToyFHE
open HeytingLean.Crypto.Lattice
open HeytingLean.Crypto.FHE
def P : MLWEParams := { n := 1, q := 17, k := 1 }
def S1 : ModVec P.k P.n P.q := fun _ _ => 1
def S2 : ModVec P.k P.n P.q := fun _ _ => 2
def Ct1 : MLWEInstance P := { A := 1, b := S1 }
def Ct2 : MLWEInstance P := { A := 1, b := S2 }
end ToyFHE

private def fhePayload : String :=
  let ok := Id.run do let _ := addCt ToyFHE.P ToyFHE.Ct1 ToyFHE.Ct2; true
  "{\"hom_add_demo\":" ++ toString ok ++ "}"

-- ZK smoke (SIS PoK)
private def zkPayload : String :=
  let p := (sisPoK toyParams 0)
  let verified := p.verify toyStmt (p.prove toyStmt (0) (by exact toyRelHolds))
  "{\"sis_pok_demo\":" ++ toString verified ++ "}"

-- PQC sentinel
private def pqcVerifiedIO : IO Bool := do
  let p1 := System.FilePath.mk "../.artifacts/pqc_verify_all.ok"
  let p2 := System.FilePath.mk ".artifacts/pqc_verify_all.ok"
  let e1 ← p1.pathExists
  if e1 then
    return true
  let e2 ← p2.pathExists
  return e2

private def readEvidenceHashIO : IO (Option String) := do
  let p1 := System.FilePath.mk "../.artifacts/pqc_verify_all.ok"
  let p2 := System.FilePath.mk ".artifacts/pqc_verify_all.ok"
  let tryRead (p : System.FilePath) : IO (Option String) := do
    if !(← p.pathExists) then return none
    try
      let s ← IO.FS.readFile p
      match Lean.Json.parse s with
      | Except.ok j =>
        match j.getObjVal? "evidence_hash" with
        | Except.ok (Lean.Json.str h) => return some h
        | _ => return none
      | _ => return none
    catch _ =>
      return none
  match (← tryRead p1) with
  | some h => return some h
  | none   => tryRead p2

private def pqcPayload (verified : Bool) (evid? : Option String) : String :=
  match evid? with
  | some h => "{\"verified\":" ++ toString verified ++ ",\"evidence_hash\":\"" ++ h ++ "\"}"
  | none    => "{\"verified\":" ++ toString verified ++ "}"

private structure Flags where
  quick : Bool := true
  full : Bool := false
  contextualityOnly : Bool := false
  valuationOnly : Bool := false
  fhezkOnly : Bool := false

private def parseFlags (args : List String) : Flags :=
  let f0 : Flags := {}
  args.foldl (init := f0) fun f a =>
    match a.trim with
    | "--quick" => { f with quick := true, full := false }
    | "--full" => { f with quick := false, full := true }
    | "--contextuality" => { f with contextualityOnly := true, valuationOnly := false, fhezkOnly := false }
    | "--valuation" => { f with contextualityOnly := false, valuationOnly := true, fhezkOnly := false }
    | "--fhe-zk" => { f with contextualityOnly := false, valuationOnly := false, fhezkOnly := true }
    | _ => f

def UnifiedDemo.main (argv : List String) : IO Unit := do
  let flags := parseFlags argv
  if flags.contextualityOnly then
    IO.println contextualityPayload; return
  if flags.valuationOnly then
    IO.println valuationPayload; return
  if flags.fhezkOnly then
    IO.println ("{" ++ "\"fhe\":" ++ fhePayload ++ ",\"zk\":" ++ zkPayload ++ "}"); return
  let pqcV ← if flags.full then pqcVerifiedIO else pure false
  let evid ← if flags.full then readEvidenceHashIO else pure none
  let payload := "{" ++
    "\"demo\":\"unified\"," ++
    "\"contextuality\":" ++ contextualityPayload ++ "," ++
    "\"physical\":" ++ physicalPayload ++ "," ++
    "\"valuation\":" ++ valuationPayload ++ "," ++
    "\"fhe\":" ++ fhePayload ++ "," ++
    "\"zk\":" ++ zkPayload ++ "," ++
    "\"pqc\":" ++ pqcPayload pqcV evid ++ "}"
  IO.println payload

end CLI
end HeytingLean

def main (argv : List String) : IO Unit := HeytingLean.CLI.UnifiedDemo.main argv
