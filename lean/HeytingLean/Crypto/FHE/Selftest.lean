import HeytingLean.Crypto.FHE.Params
import HeytingLean.Crypto.FHE.Ciphertext
import HeytingLean.Crypto.FHE.Core
import HeytingLean.Crypto.FHE.Nucleus

open IO

def assert (p : Bool) (msg : String) : IO Unit :=
  if p then pure () else throw <| IO.userError msg

def main (_args : List String) : IO UInt32 := do
  IO.println "apmt_fhe_selftest: running"
  let P := HeytingLean.Crypto.FHE.defaultParams
  let k : HeytingLean.Crypto.FHE.Key := { p := P.p }
  let c1 := HeytingLean.Crypto.FHE.enc k true
  let c0 := HeytingLean.Crypto.FHE.enc k false
  let ca := HeytingLean.Crypto.FHE.add c1 c0
  let cm := HeytingLean.Crypto.FHE.mul c1 c0
  let d1 := HeytingLean.Crypto.FHE.dec k c1
  let d0 := HeytingLean.Crypto.FHE.dec k c0
  let da := HeytingLean.Crypto.FHE.dec k ca
  let dm := HeytingLean.Crypto.FHE.dec k cm
  assert d1 "dec 1 failed"
  assert (!d0) "dec 0 failed"
  assert da "add failed (1+0)"
  assert (!dm) "mul failed (1*0)"
  let cb := HeytingLean.Crypto.FHE.boot k c1
  let db := HeytingLean.Crypto.FHE.dec k cb
  assert db "boot(dec) mismatch"
  -- grow noise through repeated mul; then refresh via J/Boot
  let cHeavy := (List.range 8).foldl (fun acc _ => HeytingLean.Crypto.FHE.Ciphertext.mul acc c1) c1
  -- decryption preserved
  assert (HeytingLean.Crypto.FHE.dec k cHeavy) "dec heavy failed"
  -- J trims noise and preserves Dec
  let cj := HeytingLean.Crypto.FHE.J P cHeavy
  have _ := HeytingLean.Crypto.FHE.noise_J_fresh P cHeavy
  have _ := HeytingLean.Crypto.FHE.Dec_preserved_by_J P cHeavy
  assert (HeytingLean.Crypto.FHE.dec k cj) "J(dec) mismatch"
  -- ensure bound holds (runtime check mirroring theorem)
  assert ((cj.noise ≤ P.B0)) "J did not trim noise"
  IO.println "apmt_fhe_selftest: ok"
  pure 0
