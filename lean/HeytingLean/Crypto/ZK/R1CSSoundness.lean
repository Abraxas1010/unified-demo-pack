import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Support
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.BoolLens

namespace HeytingLean
namespace Crypto
namespace ZK
namespace R1CSSoundness

open R1CSBool
open BoolLens

/-- The compiled R1CS system is satisfied by the canonical assignment. -/
theorem compile_satisfied {n : ℕ} (φ : Form n) (ρ : Env n) :
    System.satisfied (compile φ ρ).assignment (compile φ ρ).system := by
  classical
  -- Abbreviations matching the internal structure of `R1CSBool.compile`.
  let prog := Form.compile φ
  let result := compileTraceToR1CSFromEmpty ρ prog
  let builder := result.1
  -- Base fact: the unreversed builder system is satisfied by `builder.assign`,
  -- expressed directly at the constraint level.
  have hBuilder :
      ∀ {c}, c ∈ builder.constraints →
        Constraint.satisfied builder.assign c := by
    intro c hc
    have hBase :
        System.satisfied (compileTraceToR1CSFromEmpty ρ prog).1.assign
          (Builder.system (compileTraceToR1CSFromEmpty ρ prog).1) :=
      compileTraceToR1CSFromEmpty_satisfied (ρ := ρ) (prog := prog)
    -- Turn membership in `builder.constraints` into membership in the
    -- constraints of `Builder.system (compileTraceToR1CSFromEmpty ρ prog).1`.
    have hcSys :
        c ∈ (Builder.system (compileTraceToR1CSFromEmpty ρ prog).1).constraints := by
      simpa [Builder.system, result, builder] using hc
    have hSat :=
      hBase (c := c) hcSys
    -- Rewrite the assignment to refer to `builder`.
    simpa [result, builder] using hSat
  -- Relate `builder` back to the exported `compile` structure.
  have hAssign :
      (compile φ ρ).assignment = builder.assign := by
    simp [R1CSBool.compile, prog, result,
      compileTraceToR1CSFromEmpty, builder]
  have hSys :
      (compile φ ρ).system.constraints =
        builder.constraints.reverse := by
    simp [R1CSBool.compile, prog, result,
      compileTraceToR1CSFromEmpty, builder]
  -- Goal is definitionally `∀ {c}, c ∈ _ → Constraint.satisfied _ c`.
  intro c hc
  -- Transport membership into the reversed builder constraints.
  have hc' : c ∈ builder.constraints.reverse := by
    simpa [hSys] using hc
  -- Builder satisfies the unreversed system.
  have hBuilderList :
      System.satisfied builder.assign { constraints := builder.constraints } := by
    intro d hd
    -- `hd` ranges over `{ constraints := builder.constraints }.constraints`,
    -- which is definitionally just `builder.constraints`.
    have hd' : d ∈ builder.constraints := by
      simpa using hd
    exact hBuilder (c := d) hd'
  have hRevSys :
      System.satisfied builder.assign
        { constraints := builder.constraints.reverse } :=
    (System.satisfied_reverse
        (assign := builder.assign) (cs := builder.constraints)).mpr
      hBuilderList
  have hcRev :
      c ∈ ({ constraints := builder.constraints.reverse } : System).constraints := by
    simpa using hc'
  have hSatBuilderC :
      Constraint.satisfied builder.assign c :=
    hRevSys (c := c) hcRev
  -- Finally, rewrite the assignment to the exported `compile` structure.
  have hSatCompileC :
      Constraint.satisfied (compile φ ρ).assignment c := by
    simpa [hAssign] using hSatBuilderC
  exact hSatCompileC

/-- Completeness: the compiled system is satisfiable (witnessed by the canonical assignment). -/
theorem compile_satisfiable {n : ℕ} (φ : Form n) (ρ : Env n) :
    ∃ a, System.satisfied a (compile φ ρ).system :=
  ⟨(compile φ ρ).assignment, compile_satisfied (φ := φ) (ρ := ρ)⟩

/-- The compiled output variable encodes the boolean evaluation as a rational. -/
theorem compile_output_eval {n : ℕ} (φ : Form n) (ρ : Env n) :
    boolToRat (BoolLens.eval φ ρ) =
      (compile φ ρ).assignment (compile φ ρ).output := by
  classical
  -- Abbreviations matching the internal builder/result of `compile`.
  let prog := Form.compile φ
  let result := compileTraceToR1CSFromEmpty ρ prog
  let builder := result.1
  let stackVars := result.2
  -- From the strong invariant, we know the compiled builder matches the
  -- execution trace starting from the empty stack.
  have hMatches :
      Matches builder (BoolLens.exec ρ prog []) stackVars := by
    simpa [compileTraceToR1CSFromEmpty, prog, result,
      builder, stackVars]
      using
        (compileTraceToR1CSFromEmpty_matches (ρ := ρ) (prog := prog))
  -- exec pushes exactly the boolean eval on the stack
  have hExec : BoolLens.exec ρ prog [] = [BoolLens.eval φ ρ] := by
    simp [prog, BoolLens.exec_compile_aux]
  -- specialize Matches to the 1-element stack and extract the head equality
  have hHead : boolToRat (BoolLens.eval φ ρ) = builder.assign (stackVars.headD 0) := by
    -- rewrite matches to the singleton stack
    have h' : Matches builder [BoolLens.eval φ ρ] stackVars := by
      simpa [prog, result, builder, stackVars, hExec]
        using hMatches
    -- analyze the shape of the right list by cases; Forall₂ over a singleton
    revert h'
    cases stackVars with
    | nil =>
        intro h'
        -- impossible: Forall₂ cannot relate a nonempty list with []
        cases h'
    | @cons v vs =>
        intro h'
        -- extract the head equality from the Forall₂.cons case
        have hCons :
            Matches builder (BoolLens.eval φ ρ :: []) (v :: vs) := by
          simpa using h'
        have hHead' :
            boolToRat (BoolLens.eval φ ρ) = builder.assign v :=
          matches_cons_head (builder := builder)
            (b := BoolLens.eval φ ρ) (stack := []) (v := v) (vars := vs) hCons
        -- align with headD
        simpa using hHead'
  -- rewrite back to the `compile` structure
  simpa [R1CSBool.compile, prog, result, builder, stackVars,
    compileTraceToR1CSFromEmpty]
    using hHead

end R1CSSoundness
end ZK
end Crypto
end HeytingLean
