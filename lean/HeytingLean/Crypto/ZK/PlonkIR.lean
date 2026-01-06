import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Support
import HeytingLean.Crypto.ZK.Rename

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Plonk

open ZK

/-- For the PLONK-style IR we reuse the existing linear-combination type. -/
abbrev LinComb := ZK.LinComb

/-- A minimal gate over three PLONK slots. -/
structure Gate where
  A : LinComb
  B : LinComb := ZK.LinComb.ofConst 1
  C : LinComb

/-- A simplified PLONK system with a list of gates and a copy permutation. -/
structure System where
  gates : List Gate := []
  copyPermutation : List Nat := []

/-- Equality constraint between variables `i` and `j`. -/
def eqVarConstraint (i j : ZK.Var) : ZK.Constraint :=
  { A := ZK.LinComb.single i 1
  , B := ZK.LinComb.ofConst 1
  , C := ZK.LinComb.single j 1 }

/-- Pairs `(i, perm[i])` extracted from a permutation list. -/
def copyPairs (perm : List Nat) : List (Nat × Nat) :=
  (List.range perm.length).map (fun i => (i, perm.getD i 0))

/-- Copy-constraint system generated from a permutation. -/
def copyConstraintSystem (perm : List Nat) : ZK.System :=
  { constraints := (copyPairs perm).map (fun ij => eqVarConstraint ij.1 ij.2) }

/-- Convert the PLONK gates to a plain R1CS system. -/
def System.toR1CS (sys : System) : ZK.System :=
  { constraints := sys.gates.map (fun g => (⟨g.A, g.B, g.C⟩ : ZK.Constraint)) }

/-- Native PLONK satisfaction: R1CS satisfaction of `toR1CS sys` together with
    satisfaction of the copy-constraint system. -/
def System.satisfiedNative (assign : ZK.Var → ℚ) (sys : System) : Prop :=
  (System.toR1CS sys).satisfied assign ∧
    (copyConstraintSystem sys.copyPermutation).satisfied assign

/-- Semantic relation for PLONK-style systems, identified with `satisfiedNative`. -/
def RelPlonk (sys : System) (assign : ZK.Var → ℚ) : Prop :=
  System.satisfiedNative assign sys

@[simp] lemma relPlonk_iff_satisfiedNative (sys : System) (a : ZK.Var → ℚ) :
    RelPlonk sys a ↔ sys.satisfiedNative a :=
  Iff.rfl

/-- Reflexive equality constraints are always satisfied. -/
@[simp] lemma eqVarConstraint_refl_satisfied (a : ZK.Var → ℚ) (i : Nat) :
    ZK.Constraint.satisfied a (eqVarConstraint i i) := by
  classical
  unfold ZK.Constraint.satisfied eqVarConstraint
  simp [ZK.LinComb.eval_single, ZK.LinComb.eval_ofConst]

/-- If the assignment respects all copy pairs `(i, perm[i])`, then the copy
    system built from `perm` is satisfied. -/
lemma copySatisfied_of_pairs' (a : ZK.Var → ℚ) {perm : List Nat}
    (hPairs : ∀ ij ∈ copyPairs perm, a ij.1 = a ij.2) :
    ZK.System.satisfied a (copyConstraintSystem perm) := by
  classical
  intro c hc
  unfold copyConstraintSystem at hc
  rcases List.mem_map.1 hc with ⟨ij, hij, h_eq⟩
  rcases ij with ⟨i, j⟩
  have hEq : a i = a j := hPairs ⟨i, j⟩ hij
  have : ZK.Constraint.satisfied a (eqVarConstraint i j) := by
    simp [ZK.Constraint.satisfied, eqVarConstraint, ZK.LinComb.eval_single,
      ZK.LinComb.eval_ofConst, hEq]
  simpa [h_eq] using this

/-- Under an explicit pair-respect hypothesis, native satisfaction reduces to
    converted R1CS satisfaction. -/
lemma satisfiedNative_iff_r1cs_of_pairs (sys : System) (a : ZK.Var → ℚ)
    (hPairs : ∀ ij ∈ copyPairs sys.copyPermutation, a ij.1 = a ij.2) :
    sys.satisfiedNative a ↔ (System.toR1CS sys).satisfied a := by
  constructor
  · intro h; exact h.1
  · intro h
    have hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a :=
      copySatisfied_of_pairs' (a := a) (perm := sys.copyPermutation) hPairs
    exact And.intro h hCopy

/-- Alternative formulation of copy-satisfaction starting from a quantified
    equality hypothesis. -/
lemma copySatisfied_of_pairs (a : ZK.Var → ℚ) {perm : List Nat}
    (hPairs : ∀ {i j}, (i, j) ∈ copyPairs perm → a i = a j) :
    ZK.System.satisfied a (copyConstraintSystem perm) := by
  classical
  refine copySatisfied_of_pairs' (a := a) (perm := perm) ?h
  intro ij hij
  rcases ij with ⟨i, j⟩
  exact hPairs (i := i) (j := j) hij

/-- If the copy-constraint system built from `perm` is satisfied by `a`, then
    `a` respects every pair `(i, perm[i])`. -/
lemma pairs_of_copySatisfied (a : ZK.Var → ℚ) {perm : List Nat}
    (hCopy : ZK.System.satisfied a (copyConstraintSystem perm)) :
    ∀ ij ∈ copyPairs perm, a ij.1 = a ij.2 := by
  classical
  intro ij hij
  rcases ij with ⟨i, j⟩
  have hc : ZK.Constraint.satisfied a (eqVarConstraint i j) := by
    have hc' : (eqVarConstraint i j) ∈ (copyConstraintSystem perm).constraints := by
      unfold copyConstraintSystem
      exact List.mem_map.mpr ⟨(i, j), hij, rfl⟩
    exact hCopy hc'
  simpa [ZK.Constraint.satisfied, eqVarConstraint, ZK.LinComb.eval_single,
    ZK.LinComb.eval_ofConst] using hc

/-- Under copy-satisfaction, native semantics reduces to the converted R1CS
    semantics. -/
lemma satisfiedNative_iff_r1cs_of_copySatisfied (sys : System) (a : ZK.Var → ℚ)
    (hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a) :
    sys.satisfiedNative a ↔ (System.toR1CS sys).satisfied a := by
  have hPairs : ∀ ij ∈ copyPairs sys.copyPermutation, a ij.1 = a ij.2 :=
    pairs_of_copySatisfied (a := a) (perm := sys.copyPermutation) hCopy
  exact satisfiedNative_iff_r1cs_of_pairs (sys := sys) (a := a) (hPairs := hPairs)

/-- Local helper: all variables in a linear combination are `< n`. We keep this
    for potential future refinements; it is not used in the current soundness
    proof. -/
def linCombBound (lc : ZK.LinComb) (n : Nat) : Prop :=
  ∀ v ∈ ZK.LinComb.support lc, v < n

/-- Gate variable bound: each slot of the gate references only variables `< n`.
    The current development records this predicate but does not yet connect it
    to the σ-equivalence lemma. -/
def gateBound (g : Gate) (n : Nat) : Prop :=
  linCombBound g.A n ∧ linCombBound g.B n ∧ linCombBound g.C n

/-- Coverage helper: if the support of `toR1CS sys` is bounded by the
    permutation length, then every support variable appears as a left component
    of some pair in `copyPairs`. This is used in tests to connect explicit
    bounds to copy-coverage. -/
lemma cover_of_support_subset_range (sys : System)
    (hBound : ∀ v ∈ ZK.System.support (System.toR1CS sys), v < sys.copyPermutation.length) :
    ∀ v ∈ ZK.System.support (System.toR1CS sys), ∃ j, (v, j) ∈ copyPairs sys.copyPermutation := by
  classical
  intro v hv
  refine ⟨sys.copyPermutation.getD v 0, ?_⟩
  have hvRange : v ∈ List.range sys.copyPermutation.length := by
    exact List.mem_range.mpr (hBound v hv)
  exact List.mem_map.mpr ⟨v, hvRange, by simp [copyPairs]⟩

/-- Combine copy-satisfaction and a bound on support to obtain a σ‑renamed
    view. At this abstraction level we simply choose `σ := id`. Using
    `satisfiedNative_iff_r1cs_of_copySatisfied` and the renaming lemma
    specialised to `σ = id`, we obtain the desired equivalence. The `hBound`
    hypothesis is recorded for future refinements but not used in the proof. -/
lemma native_iff_renamed_sigma_of_bounds (sys : System) (a : ZK.Var → ℚ)
    (hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a)
    (hBound : ∀ v ∈ ZK.System.support (System.toR1CS sys), v < sys.copyPermutation.length) :
    ∃ σ, sys.satisfiedNative a ↔
      ZK.System.satisfied a (ZK.Rename.system σ (System.toR1CS sys)) := by
  classical
  have hNat : sys.satisfiedNative a ↔ (System.toR1CS sys).satisfied a :=
    satisfiedNative_iff_r1cs_of_copySatisfied (sys := sys) (a := a) (hCopy := hCopy)
  -- For `σ = id`, renaming preserves satisfaction.
  have hRename :
      (System.toR1CS sys).satisfied a ↔
        ZK.System.satisfied a (ZK.Rename.system (fun v => v) (System.toR1CS sys)) := by
    have := (ZK.Rename.satisfied_system (σ := fun v => v) (a := a)
      (sys := System.toR1CS sys))
    -- `System.satisfied a (Rename.system id S) ↔ System.satisfied (fun v => a v) S`
    simpa using this.symm
  refine ⟨(fun v => v), ?_⟩
  exact hNat.trans hRename

/-- Convenience corollary: under gate-bounds we obtain the same σ-equivalence.
    In the current model the gate-bound hypothesis is recorded but not used. -/
lemma native_iff_renamed_sigma_of_gateBounds (sys : System) (a : ZK.Var → ℚ)
    (hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a)
    (hBound : ∀ g ∈ sys.gates, gateBound g sys.copyPermutation.length) :
    ∃ σ, sys.satisfiedNative a ↔
      ZK.System.satisfied a (ZK.Rename.system σ (System.toR1CS sys)) := by
  classical
  have hNat : sys.satisfiedNative a ↔ (System.toR1CS sys).satisfied a :=
    satisfiedNative_iff_r1cs_of_copySatisfied (sys := sys) (a := a) (hCopy := hCopy)
  have hRename :
      (System.toR1CS sys).satisfied a ↔
        ZK.System.satisfied a (ZK.Rename.system (fun v => v) (System.toR1CS sys)) := by
    have := (ZK.Rename.satisfied_system (σ := fun v => v) (a := a)
      (sys := System.toR1CS sys))
    simpa using this.symm
  refine ⟨(fun v => v), ?_⟩
  exact hNat.trans hRename

end Plonk
end ZK
end Crypto
end HeytingLean
