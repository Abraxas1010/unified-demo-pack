import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSBool

/-!
Lightweight compiler variant that records which R1CS variable indices correspond
to environment pushes (`pushVar`) for a given Boolean form and environment.
This does not modify the proven compiler; it mirrors its operational behaviour
to extract mapping information for runtime verification wiring.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace R1CSBoolEnv

open BoolLens
open ZK
open R1CSBool

abbrev Var := ZK.Var

def compileWithEnvMap {n : ℕ} (φ : Form n) (ρ : Env n) : R1CSBool.Compiled × List (Nat × Var) := by
  classical
  let prog := Form.compile φ
  -- local helper to simulate `pushConst` + `recordBoolean`
  let pushConstLocal := fun (builder : R1CSBool.Builder) (value : ℚ) =>
    let (builder', v) := R1CSBool.Builder.fresh builder value
    let builder'' := R1CSBool.Builder.addConstraint builder' (R1CSBool.eqConstConstraint v value)
    let builder''' := R1CSBool.Builder.addConstraint builder'' (R1CSBool.boolConstraint v)
    (builder''', v)
  -- Replay compilation while recording mapping from env index to created var
  let rec loop
      (prog : List (Instr n))
      (before : Stack)
      (stackVars : List Var)
      (builder : R1CSBool.Builder)
      (acc : List (Nat × Var))
      : R1CSBool.Builder × List Var × List (Nat × Var) :=
    match prog with
    | [] => (builder, stackVars, acc)
    | instr :: progRest =>
      match instr with
      | .pushTop =>
          let (builder', v) := pushConstLocal builder 1
          loop progRest (step ρ instr before) (v :: stackVars) builder' acc
      | .pushBot =>
          let (builder', v) := pushConstLocal builder 0
          loop progRest (step ρ instr before) (v :: stackVars) builder' acc
      | .pushVar idx =>
          let val := if ρ idx then (1 : ℚ) else 0
          let (builder', v) := pushConstLocal builder val
          -- record env index -> var mapping
          let acc' := (idx.1, v) :: acc
          loop progRest (step ρ instr before) (v :: stackVars) builder' acc'
      | .applyAnd =>
          let after := step ρ instr before
          match before, after, stackVars with
          | _x :: _y :: _, z :: _, vx :: vy :: rest =>
              let (builder1, vz) := R1CSBool.Builder.fresh builder (if z then (1 : ℚ) else 0)
              let builder2 :=
                R1CSBool.Builder.addConstraint builder1
                  { A := LinComb.single vx 1
                    B := LinComb.single vy 1
                    C := LinComb.single vz 1 }
              let builder3 := R1CSBool.Builder.addConstraint builder2 (R1CSBool.boolConstraint vz)
              loop progRest after (vz :: rest) builder3 acc
          | _, _, _ => loop progRest after stackVars builder acc
      | .applyOr =>
          let after := step ρ instr before
          match before, after, stackVars with
          | x :: y :: _, z :: _, vx :: vy :: rest =>
              let mulVal := if (y && x) then (1 : ℚ) else 0
              let (builder1, vmul) := R1CSBool.Builder.fresh builder mulVal
              let builder2 :=
                R1CSBool.Builder.addConstraint builder1
                  { A := LinComb.single vy 1
                    B := LinComb.single vx 1
                    C := LinComb.single vmul 1 }
              let builder3 := R1CSBool.Builder.addConstraint builder2 (R1CSBool.boolConstraint vmul)
              let (builder4, vz) := R1CSBool.Builder.fresh builder3 (if z then (1 : ℚ) else 0)
              let builder5 :=
                R1CSBool.Builder.addConstraint builder4
                  (R1CSBool.eqConstraint (R1CSBool.linhead_or vz vx vy vmul) (LinComb.ofConst 0))
              let builder6 := R1CSBool.Builder.addConstraint builder5 (R1CSBool.boolConstraint vz)
              loop progRest after (vz :: rest) builder6 acc
          | _, _, _ => loop progRest after stackVars builder acc
      | .applyImp =>
          let after := step ρ instr before
          match before, after, stackVars with
          | x :: y :: _, z :: _, vx :: vy :: rest =>
              let mulVal := if (y && x) then (1 : ℚ) else 0
              let (builder1, vmul) := R1CSBool.Builder.fresh builder mulVal
              let builder2 :=
                R1CSBool.Builder.addConstraint builder1
                  { A := LinComb.single vy 1
                    B := LinComb.single vx 1
                    C := LinComb.single vmul 1 }
              let builder3 := R1CSBool.Builder.addConstraint builder2 (R1CSBool.boolConstraint vmul)
              let (builder4, vz) := R1CSBool.Builder.fresh builder3 (if z then (1 : ℚ) else 0)
              let builder5 :=
                R1CSBool.Builder.addConstraint builder4
                  (R1CSBool.eqConstraint (R1CSBool.linhead_imp vz vx vy vmul) (LinComb.ofConst 0))
              let builder6 := R1CSBool.Builder.addConstraint builder5 (R1CSBool.boolConstraint vz)
              loop progRest after (vz :: rest) builder6 acc
          | _, _, _ => loop progRest after stackVars builder acc
  let (builder, stackVars, envMap) := loop prog [] [] {} []
  -- Assemble compiled object mirroring R1CSBool.compile
  let outputVar := stackVars.headD 0
  let compiled : R1CSBool.Compiled :=
    { system := { constraints := builder.constraints.reverse }
      assignment := builder.assign
      output := outputVar }
  exact (compiled, envMap.reverse)

end R1CSBoolEnv
end ZK
end Crypto
end HeytingLean
