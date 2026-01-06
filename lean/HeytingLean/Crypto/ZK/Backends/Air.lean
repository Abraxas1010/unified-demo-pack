import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.IR
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSSoundness
import HeytingLean.Crypto.ZK.Support
import HeytingLean.Crypto.ZK.AirIR

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Backends

open BoolLens
open R1CSBool
open Crypto.ZK.AIR

structure AirSys where
  system : AIR.System
  output : Var

def AirAssign := Var → ℚ

def airCompile {n : ℕ} (ρ : Env n) (prog : HeytingLean.Crypto.Program n) : AirSys :=
  let trace := BoolLens.traceFrom ρ prog []
  let result := R1CSBool.compileTraceToR1CSFromEmpty ρ prog
  let builder := result.1
  let stackVars := result.2
  let sys : AIR.System :=
    { trace := { width := 3, length := trace.length }
    , r1cs  := { constraints := builder.constraints.reverse } }
  let out : Var := stackVars.headD 0
  { system := sys, output := out }

def airSatisfies (s : AirSys) (a : AirAssign) : Prop :=
  ZK.System.satisfied a s.system.r1cs

def airPublic (s : AirSys) (a : AirAssign) : List ℚ := [a s.output]

def AirBackend : ZK.IR.Backend ℚ :=
  { Sys := AirSys
  , Assign := AirAssign
  , compile := fun ρ prog => airCompile ρ prog
  , satisfies := fun s a => airSatisfies s a
  , publicOut := fun s a => airPublic s a }

/-- Soundness of the AIR backend: the canonical assignment produced by
`compileTraceToR1CSFromEmpty` satisfies the AIR system embedded in
`airCompile`, and its public output bit agrees with the Boolean
evaluation of the original form. -/
theorem air_sound {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : Env n) :
  let p := HeytingLean.Crypto.Form.compile φ
  let s := airCompile ρ p
  let res := R1CSBool.compileTraceToR1CSFromEmpty ρ p
  let builder := res.1
  let assign : AirAssign := builder.assign
  airSatisfies s assign ∧ airPublic s assign = [if BoolLens.eval φ ρ then 1 else 0] := by
  classical
  intro p s res builder assign
  -- Base R1CS fact: the builder system (before reversing constraints)
  -- is satisfied by `builder.assign`.
  have hBase :
      ZK.System.satisfied
        (R1CSBool.compileTraceToR1CSFromEmpty ρ p).1.assign
        (R1CSBool.Builder.system
          (R1CSBool.compileTraceToR1CSFromEmpty ρ p).1) :=
    R1CSBool.compileTraceToR1CSFromEmpty_satisfied (ρ := ρ) (prog := p)
  -- Extract a constraint-wise view for the unreversed builder
  -- constraints.
  have hBuilder :
      ∀ {c}, c ∈ builder.constraints →
        Constraint.satisfied builder.assign c := by
    intro c hc
    have hcSys :
        c ∈ (R1CSBool.Builder.system
          (R1CSBool.compileTraceToR1CSFromEmpty ρ p).1).constraints := by
      simpa [R1CSBool.Builder.system, res, builder] using hc
    have hSatC := hBase (c := c) hcSys
    simpa [res, builder] using hSatC
  -- Package this as satisfaction of the unreversed builder system.
  have hBuilderList :
      ZK.System.satisfied builder.assign
        { constraints := builder.constraints } := by
    intro c hc
    have hc' : c ∈ builder.constraints := by
      simpa using hc
    exact hBuilder (c := c) hc'
  -- Reverse constraints to match the AIR system used by `airCompile`.
  have hSatRev :
      ZK.System.satisfied builder.assign
        { constraints := builder.constraints.reverse } :=
    (ZK.System.satisfied_reverse
        (assign := builder.assign) (cs := builder.constraints)).mpr
      hBuilderList
  -- Use the compiled output-equality lemma to identify the public bit.
  have hOutEval := R1CSSoundness.compile_output_eval (φ := φ) (ρ := ρ)
  refine And.intro ?hsat ?hout
  ·
    -- Relate the reversed builder system to the AIR system stored in `s`.
    have hSatAir :
        ZK.System.satisfied builder.assign s.system.r1cs := by
      simpa [airCompile, res, builder] using hSatRev
    -- `assign` is definitionally `builder.assign`.
    simpa [airSatisfies, assign] using hSatAir
  ·
    -- Output correctness: connect `compile_output_eval` to the AIR
    -- system's designated output, then rewrite `boolToRat` to `0/1`.
    have hOutEval' :
        builder.assign s.output = boolToRat (BoolLens.eval φ ρ) := by
      -- `compile_output_eval` talks about the `compile` structure, which
      -- is built from the same builder and stack variables used in
      -- `airCompile`. We rewrite its statement to this builder view.
      have h' :
          boolToRat (BoolLens.eval φ ρ) =
            builder.assign s.output := by
        simpa [airCompile, p, res, builder] using hOutEval
      exact h'.symm
    have hBool :
        boolToRat (BoolLens.eval φ ρ) =
          (if BoolLens.eval φ ρ then 1 else 0) := by
      cases hEval : BoolLens.eval φ ρ <;>
        simp [boolToRat, hEval]
    have hOut :
        builder.assign s.output =
          (if BoolLens.eval φ ρ then 1 else 0) := by
      calc
        builder.assign s.output
            = boolToRat (BoolLens.eval φ ρ) := hOutEval'
        _ = (if BoolLens.eval φ ρ then 1 else 0) := hBool
    -- `assign` is definitionally `builder.assign`.
    simpa [airPublic, assign, hOut]

theorem air_complete {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : Env n) :
  let p := HeytingLean.Crypto.Form.compile φ
  let s := airCompile ρ p
  ∃ as, airSatisfies s as ∧ airPublic s as = [if BoolLens.eval φ ρ then 1 else 0] := by
  classical
  intro p s
  let res := R1CSBool.compileTraceToR1CSFromEmpty ρ p
  let builder := res.1
  refine ⟨builder.assign, ?_⟩
  simpa [airCompile, airSatisfies, airPublic] using
    air_sound (φ := φ) (ρ := ρ)

end Backends
end ZK
end Crypto
end HeytingLean
