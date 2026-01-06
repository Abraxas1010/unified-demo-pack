/-
# Crypto.ZK.Spec.Cairo

Abstract execution-correctness skeleton for a Cairo-style VM.

At this level we:
* keep programs, states, traces, and semantic relations abstract;
* package the intended "trace ↔ semantics" correspondence into a
  `Model` record; and
* expose a bundled `ExecutionCorrectnessStatement` together with a
  trivial example instance.

Concrete Cairo IR / bytecode, step functions, and zk-STARK backends
are intentionally left to later refinements; they are expected to
instantiate `Model` and discharge its fields from a genuine VM
semantics.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace Cairo

/-- Abstract Cairo-style execution model.

  * `Program` is the type of programs.
  * `State` is the type of machine states.
  * `Trace` is the type of execution traces.
  * `execTrace p s₀ tr` is the final state reached by executing
    program `p` from initial state `s₀` along trace `tr`.
  * `Semantics p s₀ s₁` is the intended small- or big-step semantic
    relation between initial and final states.
  * `sound` states that any state produced by `execTrace` is
    semantically reachable.
  * `complete` states that any semantically reachable state can be
    realised by some trace. -/
structure Model where
  Program   : Type
  State     : Type
  Trace     : Type
  execTrace : Program → State → Trace → State
  Semantics : Program → State → State → Prop
  sound :
    ∀ {p : Program} {s₀ : State} {tr : Trace},
      Semantics p s₀ (execTrace p s₀ tr)
  complete :
    ∀ {p : Program} {s₀ s₁ : State},
      Semantics p s₀ s₁ → ∃ tr : Trace, execTrace p s₀ tr = s₁

/-- Bundled Cairo-execution correctness statement for a fixed model:
    execution along traces coincides with the semantic relation. -/
def ExecutionCorrectnessStatement (M : Model) : Prop :=
  (∀ {p : M.Program} {s₀ : M.State} {tr : M.Trace},
      M.Semantics p s₀ (M.execTrace p s₀ tr)) ∧
  (∀ {p : M.Program} {s₀ s₁ : M.State},
      M.Semantics p s₀ s₁ → ∃ tr : M.Trace, M.execTrace p s₀ tr = s₁)

/-- `ExecutionCorrectnessStatement M` holds for any abstract model `M`
    by definition of its `sound` and `complete` fields. -/
theorem executionCorrectnessStatement_holds (M : Model) :
    ExecutionCorrectnessStatement M := by
  refine And.intro ?hSound ?hComplete
  · intro p s₀ tr
    exact M.sound
  · intro p s₀ s₁ h
    exact M.complete h

/-! ## Example Cairo instance

As a concrete sanity check we define a minimal "example Cairo" instance:
programs are trivial, states are natural numbers, traces are natural
numbers, and execution increments the state by the trace length. The
semantics simply states that a final state is reachable iff it can be
obtained by adding some natural number to the initial state.
-/

namespace Example

/-- Example program type (single, trivial program). -/
def Program := Unit

/-- Example state type: natural numbers. -/
def State := Nat

/-- Example trace type: lists of unit steps, each representing one
    increment of the state. -/
def Trace := List Unit

/-- One-step transition for the example VM: increment the state by one. -/
def step (_ : Program) (s s' : State) : Prop :=
  s' = s.succ

/-- Example execution: increment the state by the trace length. -/
def execTrace (_ : Program) (s₀ : State) (tr : Trace) : State :=
  tr.foldl (fun s _ => s.succ) s₀

/-- Example semantics: a final state is reachable iff it differs from the
    initial state by some natural-number offset. -/
def Semantics (_ : Program) (s₀ s₁ : State) : Prop :=
  ∃ tr : Trace, s₁ = execTrace () s₀ tr

/-- Concrete example Cairo model instantiating `Model`. -/
def model : Model :=
  { Program := Program
    , State := State
    , Trace := Trace
    , execTrace := execTrace
    , Semantics := Semantics
    , sound := by
        intro p s₀ tr
        unfold Semantics execTrace
        refine ⟨tr, rfl⟩
    , complete := by
        intro p s₀ s₁ h
        rcases h with ⟨tr, hEq⟩
        refine ⟨tr, ?_⟩
        -- `hEq` has type `s₁ = execTrace () s₀ tr`; rewrite to match the goal.
        have hEq' : execTrace () s₀ tr = s₁ := hEq.symm
        simpa [execTrace] using hEq' }

/-- The example Cairo model satisfies the bundled execution-correctness
    statement. -/
theorem model_executionCorrectness :
    ExecutionCorrectnessStatement model :=
  executionCorrectnessStatement_holds model

end Example

end Cairo
end Spec
end ZK
end Crypto
end HeytingLean
