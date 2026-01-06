import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSSoundness
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.BoolLens

/-
# Crypto.ZK.Spec.R1CS

Thin specification façade for the R1CS compilation of Boolean `Form`s.

This module:
* exposes the compiled R1CS system and assignment for a given `Form`/env;
* defines a simple satisfaction relation `Rel` over assignments; and
* re-packages the core soundness lemmas from `R1CSSoundness` as spec-level
  statements that other modules can depend on.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace R1CS

open ZK
open R1CSBool
open R1CSSoundness
open BoolLens

/-- Boolean environment used by the R1CS compiler. -/
abbrev Env (n : ℕ) := BoolLens.Env n

/-- Compiled R1CS artefacts for a Boolean form and environment. -/
def compiled {n : ℕ} (φ : Form n) (ρ : Env n) : R1CSBool.Compiled :=
  R1CSBool.compile φ ρ

/-- The R1CS system obtained from compiling a Boolean form. -/
def system {n : ℕ} (φ : Form n) (ρ : Env n) : System :=
  (compiled (φ := φ) (ρ := ρ)).system

/-- The canonical assignment associated with the compiled R1CS system. -/
def assignment {n : ℕ} (φ : Form n) (ρ : Env n) : Var → ℚ :=
  (compiled (φ := φ) (ρ := ρ)).assignment

/-- The distinguished output variable of the compiled system. -/
def output {n : ℕ} (φ : Form n) (ρ : Env n) : Var :=
  (compiled (φ := φ) (ρ := ρ)).output

/-- Specification-level relation: an assignment satisfies the compiled
    R1CS system for `(φ, ρ)`. -/
def Rel {n : ℕ} (φ : Form n) (ρ : Env n) (a : Var → ℚ) : Prop :=
  System.satisfied a (system (φ := φ) (ρ := ρ))

/-- The canonical assignment returned by the compiler satisfies the
    compiled R1CS system. -/
theorem assignment_satisfies {n : ℕ} (φ : Form n) (ρ : Env n) :
    Rel (φ := φ) (ρ := ρ) (assignment (φ := φ) (ρ := ρ)) := by
  unfold Rel assignment system compiled
  exact compile_satisfied (φ := φ) (ρ := ρ)

/-- There exists at least one satisfying assignment for the compiled
    R1CS system associated to `(φ, ρ)`. -/
theorem exists_satisfying {n : ℕ} (φ : Form n) (ρ : Env n) :
    ∃ a, Rel (φ := φ) (ρ := ρ) a := by
  unfold Rel system compiled
  -- `compile_satisfiable` already provides the existential witness.
  simpa using (compile_satisfiable (φ := φ) (ρ := ρ))

/-- The compiled output variable encodes the Boolean evaluation via the
    canonical assignment. This is the spec-level bridge between the
    Boolean semantics and the R1CS witness. -/
theorem output_eval {n : ℕ} (φ : Form n) (ρ : Env n) :
    boolToRat (BoolLens.eval φ ρ) =
      assignment (φ := φ) (ρ := ρ) (output (φ := φ) (ρ := ρ)) := by
  unfold assignment output compiled
  exact compile_output_eval (φ := φ) (ρ := ρ)

/-- Bundled R1CS satisfiability statement: every compiled Boolean form
    admits at least one satisfying assignment for its R1CS encoding. -/
def SatisfiabilityStatement : Prop :=
  ∀ {n : ℕ} (φ : Form n) (ρ : Env n),
    ∃ a, Rel (φ := φ) (ρ := ρ) a

/-- `SatisfiabilityStatement` holds, witnessed directly by the
    `exists_satisfying` lemma. -/
theorem satisfiabilityStatement_holds : SatisfiabilityStatement := by
  intro n φ ρ
  simpa using (exists_satisfying (φ := φ) (ρ := ρ))

/-- Bundled circuit-compilation correctness statement: for every Boolean
    form and environment, the compiler’s canonical assignment both
    satisfies the compiled R1CS system and encodes the Boolean
    evaluation at the distinguished output variable. -/
def CompilationCorrectnessStatement : Prop :=
  ∀ {n : ℕ} (φ : Form n) (ρ : Env n),
    Rel (φ := φ) (ρ := ρ) (assignment (φ := φ) (ρ := ρ)) ∧
      boolToRat (BoolLens.eval φ ρ) =
        assignment (φ := φ) (ρ := ρ) (output (φ := φ) (ρ := ρ))

/-- `CompilationCorrectnessStatement` holds, combining
    `assignment_satisfies` and `output_eval`. -/
theorem compilationCorrectnessStatement_holds :
    CompilationCorrectnessStatement := by
  intro n φ ρ
  refine And.intro ?hSat ?hOut
  · exact assignment_satisfies (φ := φ) (ρ := ρ)
  · exact output_eval (φ := φ) (ρ := ρ)

end R1CS
end Spec
end ZK
end Crypto
end HeytingLean
