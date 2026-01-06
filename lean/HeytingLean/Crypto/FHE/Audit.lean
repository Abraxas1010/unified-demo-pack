import Lean

open IO

def runBash (cmd : String) : IO (String × String × UInt32) := do
  let p ← IO.Process.spawn { cmd := "bash", args := #["-lc", cmd], stderr := .piped, stdout := .piped }
  let out ← p.stdout.readToEnd
  let err ← p.stderr.readToEnd
  let code ← p.wait
  pure (out, err, code)

def main (args : List String) : IO UInt32 := do
  let distArg := match args with | d :: _ => d | _ => "dist/apmt_fhe"
  let dist := if distArg.startsWith "../" then distArg.drop 3 else distArg
  let cmd := s!"if [ -x ./scripts/fhe_audit.sh ]; then ./scripts/fhe_audit.sh '{dist}'; elif [ -x ../scripts/fhe_audit.sh ]; then (cd .. && ./scripts/fhe_audit.sh '{dist}'); elif [ -x ../../scripts/fhe_audit.sh ]; then (cd ../.. && ./scripts/fhe_audit.sh '{dist}'); else echo 'fhe_audit.sh not found' >&2; exit 1; fi"
  let (out, err, code) ← runBash cmd
  if code == 0 then
    IO.println out.trim
    pure 0
  else
    IO.eprintln err.trim
    pure 1
