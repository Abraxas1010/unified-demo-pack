import HeytingLean.Crypto.ZK.AirIR

/-
# Crypto.ZK.Spec.AIR

Specification façade for the simplified AIR (STARK) IR.

At this stage the AIR semantics are modelled as R1CS satisfaction of the
embedded `System.r1cs` field. This provides a stable relation `Rel` that
later, more detailed AIR/trace semantics can refine.
-/

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Spec
namespace AIR

open ZK
open Crypto.ZK.AIR

/-- Spec-level satisfaction relation for an AIR system: for now, this is
    simply R1CS satisfaction of the embedded `r1cs` system. -/
def Rel (sys : AIR.System) (a : ZK.Var → ℚ) : Prop :=
  sys.r1cs.satisfied a

/-- In the current model, `Rel` is definitionally equal to R1CS
    satisfaction of the embedded system. This packages the intended
    "constraints correctness" property for the `airConstraintsCorrectness`
    master-list row. -/
@[simp] theorem Rel_iff_r1cs (sys : AIR.System) (a : ZK.Var → ℚ) :
    Rel sys a ↔ sys.r1cs.satisfied a := Iff.rfl

/-- Bundled AIR-constraints correctness statement: the spec-level relation
    `Rel` coincides with R1CS satisfaction of the embedded `r1cs`
    system for all AIR systems and assignments. -/
def ConstraintsCorrectnessStatement : Prop :=
  ∀ (sys : AIR.System) (a : ZK.Var → ℚ),
    Rel sys a ↔ sys.r1cs.satisfied a

/-- `ConstraintsCorrectnessStatement` holds, witnessed directly by the
    definitional equality `Rel_iff_r1cs`. -/
theorem constraintsCorrectnessStatement_holds :
    ConstraintsCorrectnessStatement := by
  intro sys a
  exact Rel_iff_r1cs sys a

/-- A trace of assignments for an AIR system: for each time index less
    than `sys.trace.length`, we have a full R1CS assignment. This is a
    minimal, trace-level view that future AIR semantics can refine. -/
def Trace (sys : AIR.System) :=
  Fin sys.trace.length → (ZK.Var → ℚ)

/-- Trace-level satisfaction: every row in the trace yields an
    assignment that satisfies the embedded R1CS system. -/
def TraceRel (sys : AIR.System) (tr : Trace sys) : Prop :=
  ∀ t : Fin sys.trace.length, sys.r1cs.satisfied (tr t)

/-- Constant trace built from a single assignment: every time index
    maps to the same underlying assignment. -/
def constTrace (sys : AIR.System) (a : ZK.Var → ℚ) : Trace sys :=
  fun _ => a

/-- Completeness direction for the simple trace semantics: any
    assignment that satisfies the embedded R1CS system gives rise to a
    trace that satisfies `TraceRel` by repetition. -/
lemma TraceRel_of_r1cs (sys : AIR.System) (a : ZK.Var → ℚ)
    (h : sys.r1cs.satisfied a) :
    TraceRel sys (constTrace sys a) := by
  intro t
  -- `constTrace sys a t` is definitionally equal to `a`, so this goal
  -- reduces to `sys.r1cs.satisfied a`.
  change sys.r1cs.satisfied a
  exact h

/-- Soundness direction for the simple trace semantics: if a trace
    satisfies `TraceRel`, then every row assignment in the trace
    satisfies the embedded R1CS system. -/
lemma r1cs_of_TraceRel (sys : AIR.System) (tr : Trace sys)
    (t : Fin sys.trace.length) (h : TraceRel sys tr) :
    sys.r1cs.satisfied (tr t) :=
  h t

/-- Bundled trace-level correctness statement for AIR: any R1CS
    satisfying assignment extends to a satisfying trace (via
    `constTrace`), and any satisfying trace consists entirely of
    R1CS-satisfying row assignments. This is a first trace-level
    refinement of `ConstraintsCorrectnessStatement`. -/
def TraceConstraintsCorrectnessStatement : Prop :=
  ∀ (sys : AIR.System),
    (∀ a : ZK.Var → ℚ,
      sys.r1cs.satisfied a → TraceRel sys (constTrace sys a)) ∧
    (∀ tr : Trace sys,
      TraceRel sys tr → ∀ t : Fin sys.trace.length,
        sys.r1cs.satisfied (tr t))

/-- `TraceConstraintsCorrectnessStatement` holds directly from
    `TraceRel_of_r1cs` and `r1cs_of_TraceRel`. -/
theorem traceConstraintsCorrectnessStatement_holds :
    TraceConstraintsCorrectnessStatement := by
  intro sys
  refine And.intro ?hComp ?hSound
  · intro a hSat
    exact TraceRel_of_r1cs sys a hSat
  · intro tr hTrace t
    exact r1cs_of_TraceRel sys tr t hTrace

/-- Convenience helper: the transition set obtained by auto-classifying
    constraints of the embedded R1CS system. This is a purely structural
    view that later semantics can build on. -/
def transitions (sys : AIR.System) : AIR.TransitionSet :=
  AIR.TransitionSet.ofSystemAuto sys.r1cs.constraints

end AIR
end Spec
end ZK
end Crypto
end HeytingLean
