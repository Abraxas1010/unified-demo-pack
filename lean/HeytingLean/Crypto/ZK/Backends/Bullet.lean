import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.BulletIR
import HeytingLean.Crypto.ZK.IR
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSSoundness
import HeytingLean.Crypto.ZK.Support

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Backends

open BoolLens
open R1CSBool

structure BulletSys where
  system : Bullet.System
  output : Var

def BulletAssign := Var → ℚ

def bulletCompile {n : ℕ} (ρ : Env n) (prog : HeytingLean.Crypto.Program n) : BulletSys :=
  let result := R1CSBool.compileTraceToR1CSFromEmpty (ρ := ρ) prog
  let builder := result.1
  let stackVars := result.2
  -- create labels for each variable index as a minimal commitment list
  let labels := (List.range builder.nextVar).map (fun i => Bullet.Commitment.mk s!"v{i}")
  let sys : Bullet.System := { commitments := labels, r1cs := { constraints := builder.constraints.reverse } }
  let out : Var := stackVars.headD 0
  { system := sys, output := out }

def bulletSatisfies (s : BulletSys) (a : BulletAssign) : Prop :=
  s.system.r1cs.satisfied a

def bulletPublic (s : BulletSys) (a : BulletAssign) : List ℚ := [a s.output]

def BulletBackend : ZK.IR.Backend ℚ :=
  { Sys := BulletSys
  , Assign := BulletAssign
  , compile := fun ρ prog => bulletCompile ρ prog
  , satisfies := fun s a => bulletSatisfies s a
  , publicOut := fun s a => bulletPublic s a }

theorem bullet_sound {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : Env n) :
  let p := HeytingLean.Crypto.Form.compile φ
  let s := bulletCompile ρ p
  let res := R1CSBool.compileTraceToR1CSFromEmpty (ρ := ρ) p
  let builder := res.1
  let assign : BulletAssign := builder.assign
  bulletSatisfies s assign ∧ bulletPublic s assign = [if BoolLens.eval φ ρ then 1 else 0] := by
  classical
  intro p s res builder assign
  have hBase :
      System.satisfied builder.assign (R1CSBool.Builder.system builder) := by
    -- Avoid dot-notation reductions (`builder.system.constraints`) causing
    -- mismatched definitional unfoldings in `simpa`.
    change System.satisfied builder.assign { constraints := builder.constraints }
    -- Unfold both sides down to the constraint list.
    change ∀ {c}, c ∈ builder.constraints → Constraint.satisfied builder.assign c
    intro c hc
    have hAll :
        System.satisfied (R1CSBool.compileTraceToR1CSFromEmpty (ρ := ρ) p).1.assign
          (R1CSBool.Builder.system
            (R1CSBool.compileTraceToR1CSFromEmpty (ρ := ρ) p).1) :=
      (R1CSBool.compileTraceToR1CSFromEmpty_satisfied (ρ := ρ) (prog := p))
    have hc' :
        c ∈ (R1CSBool.Builder.system
            (R1CSBool.compileTraceToR1CSFromEmpty (ρ := ρ) p).1).constraints := by
      simpa [R1CSBool.Builder.system, res, builder] using hc
    have hSatC := hAll (c := c) hc'
    simpa [res, builder] using hSatC
  have hSatOrig : System.satisfied assign { constraints := builder.constraints } := by
    intro c hc
    have hc' : c ∈ (R1CSBool.Builder.system builder).constraints := by
      simpa [R1CSBool.Builder.system] using hc
    have hSat := hBase (c := c) hc'
    simpa [assign] using hSat

  have hSatSys : bulletSatisfies s assign := by
    -- `bulletCompile` stores the constraint list in reversed order, but
    -- satisfaction is invariant under list permutations.
    dsimp [bulletSatisfies]
    change ∀ {c}, c ∈ s.system.r1cs.constraints → Constraint.satisfied assign c
    intro c hc
    have hc' : c ∈ builder.constraints.reverse := by
      simpa [bulletCompile, p, s, res, builder] using hc
    have hc'' : c ∈ builder.constraints := by
      simpa using (List.mem_reverse.1 hc')
    exact hSatOrig (c := c) hc''

  have hOutEval : boolToRat (BoolLens.eval φ ρ) = assign s.output := by
    simpa [R1CSBool.compile, R1CSBool.compileTraceToR1CSFromEmpty,
      bulletCompile, p, s, res, builder, assign] using
      (R1CSSoundness.compile_output_eval (φ := φ) (ρ := ρ))
  refine And.intro ?hsat ?hout
  · exact hSatSys
  · cases hEval : BoolLens.eval φ ρ <;>
      simp [bulletPublic, boolToRat, hEval] at hOutEval ⊢ <;>
      simpa using hOutEval.symm

theorem bullet_complete {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : Env n) :
  let p := HeytingLean.Crypto.Form.compile φ
  let s := bulletCompile ρ p
  ∃ as, bulletSatisfies s as ∧ bulletPublic s as = [if BoolLens.eval φ ρ then 1 else 0] := by
  classical
  intro p s
  let res := R1CSBool.compileTraceToR1CSFromEmpty (ρ := ρ) p
  let builder := res.1
  let assign : BulletAssign := builder.assign
  refine ⟨assign, ?_⟩
  simpa [res, builder, assign] using bullet_sound (φ := φ) (ρ := ρ)

end Backends
end ZK
end Crypto
end HeytingLean
