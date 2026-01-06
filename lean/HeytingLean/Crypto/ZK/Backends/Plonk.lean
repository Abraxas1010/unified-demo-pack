import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.IR
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSSoundness
import HeytingLean.Crypto.ZK.Support
import HeytingLean.Crypto.ZK.PlonkIR

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Backends

open BoolLens
open R1CSBool

/-- System used by the PLONK-style backend wrapper: reuse the R1CS system and
    carry the output wire id. -/
structure PlonkSys where
  system : Plonk.System
  output : Var

def PlonkAssign := Var → ℚ

/-- Compile a BoolLens program into the wrapped system by delegating to the
    existing R1CS builder pipeline, starting from the empty stack. -/
def plonkCompile {n : ℕ} (ρ : Env n) (prog : HeytingLean.Crypto.Program n) : PlonkSys :=
  let result := R1CSBool.compileTraceToR1CSFromEmpty ρ prog
  let builder := result.1
  let stackVars := result.2
  let gates : List Plonk.Gate :=
    (builder.constraints.reverse).map (fun c => { A := c.A, B := c.B, C := c.C })
  -- In this backend we do not enforce any non-trivial copy-permutation
  -- constraints at the IR level, so we reuse only the gate list and leave
  -- `copyPermutation` empty.
  let copyPerm : List Nat := []
  let sys : Plonk.System := { gates := gates, copyPermutation := copyPerm }
  let out : Var := stackVars.headD 0
  { system := sys, output := out }

/-- Satisfaction relation delegates to the underlying R1CS system. -/
def plonkSatisfies (s : PlonkSys) (a : PlonkAssign) : Prop :=
  let r1 := Plonk.System.toR1CS s.system
  ZK.System.satisfied a r1

/-- Public output: decode the Boolean result from the assignment and output var. -/
def plonkPublic (s : PlonkSys) (a : PlonkAssign) : List ℚ :=
  [a s.output]

/-- Backend instance specialising the generic interface. -/
def PlonkBackend : ZK.IR.Backend ℚ :=
  { Sys := PlonkSys
  , Assign := PlonkAssign
  , compile := fun ρ prog => plonkCompile ρ prog
  , satisfies := fun s a => plonkSatisfies s a
  , publicOut := fun s a => plonkPublic s a }

end Backends
end ZK
end Crypto
end HeytingLean
