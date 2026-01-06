import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import HeytingLean.LoF.CryptoSheaf.Quantum.ContextualitySite

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Quantum

open Classical

-- Silence stylistic linters locally for this witness file (strict build uses --wfail)
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

-- Empirical model with possibilistic supports over a fixed finite cover
structure EmpiricalModel (cover : Finset Context) where
  support : ∀ {C : Context}, C ∈ cover → Set (Assignment C)
  nonempty : ∀ {C} (hC : C ∈ cover), (support hC).Nonempty
  compatible :
    ∀ {C1} (h1 : C1 ∈ cover) {C2} (h2 : C2 ∈ cover),
      Set.image (fun s => restrictAssign (inter_subset_left C1 C2) s) (support h1) =
      Set.image (fun s => restrictAssign (inter_subset_right C1 C2) s) (support h2)

-- A global section relative to a chosen global context X, given inclusions cover ⊆ X
def HasGlobalSection (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  ∃ g : Assignment X,
    ∀ {C} (hC : C ∈ cover),
      restrictAssign (coverSubX hC) g ∈ e.support hC

def NoGlobalSection (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  ¬ HasGlobalSection X cover e coverSubX

-- Triangle parity obstruction -------------------------------------------------

-- The cover {ab, bc, ac}
def triangleCover : Finset Context :=
  ([C_ab, C_bc, C_ac] : List Context).toFinset

@[simp] theorem mem_triangleCover {C : Context} :
    C ∈ triangleCover ↔ C = C_ab ∨ C = C_bc ∨ C = C_ac := by
  classical
  unfold triangleCover
  simp

-- Cardiniality audit invariant for the CLI cover size
@[simp] lemma triangleCover_card : triangleCover.card = 3 := by
  -- computation over a concrete finite set
  decide

-- Inclusions into the global context X_abc
@[simp] theorem triangle_cover_subset_X
    {C : Context} (hC : C ∈ triangleCover) : C ⊆ X_abc := by
  rcases (mem_triangleCover).1 hC with h | h | h
  · simpa [h] using subset_ab_abc
  · simpa [h] using subset_bc_abc
  · simpa [h] using subset_ac_abc

-- Compute `support` on concrete contexts (proved after `triangleModel` definition)
-- Handy membership proofs (inside namespace)
@[simp] lemma ab_in_cover : C_ab ∈ triangleCover := by simpa [triangleCover]
@[simp] lemma bc_in_cover : C_bc ∈ triangleCover := by simpa [triangleCover]
@[simp] lemma ac_in_cover : C_ac ∈ triangleCover := by simpa [triangleCover]

-- Named elements in each context (for constraints)
def a_in_ab : MeasIn C_ab := ⟨a, a_mem_ab⟩
def b_in_ab : MeasIn C_ab := ⟨b, b_mem_ab⟩
def b_in_bc : MeasIn C_bc := ⟨b, b_mem_bc⟩
def c_in_bc : MeasIn C_bc := ⟨c, c_mem_bc⟩
def a_in_ac : MeasIn C_ac := ⟨a, a_mem_ac⟩
def c_in_ac : MeasIn C_ac := ⟨c, c_mem_ac⟩

-- Local supports encoding the parity constraints
def supportAB : Set (Assignment C_ab) := { s | s a_in_ab = s b_in_ab }
def supportBC : Set (Assignment C_bc) := { s | s b_in_bc = s c_in_bc }
def supportAC : Set (Assignment C_ac) := { s | s a_in_ac ≠ s c_in_ac }

-- Nonemptiness proofs for each constraint set
theorem supportAB_nonempty : supportAB.Nonempty := by
  refine ⟨(fun _ => False), ?_⟩; simp [supportAB]

theorem supportBC_nonempty : supportBC.Nonempty := by
  refine ⟨(fun _ => False), ?_⟩; simp [supportBC]

theorem supportAC_nonempty : supportAC.Nonempty := by
  classical
  refine ⟨(fun x => if x.1 = a then True else False), ?_⟩
  simp [supportAC, a_in_ac, c_in_ac]

-- Overlap images coincide (compatibility) for each pair
-- Simple builders used in compatibility proofs
def constAssign (U : Context) (v : Bool) : Assignment U := fun _ => v

def acAssign (v : Bool) : Assignment C_ac :=
  fun x => if x.1 = a then v else !v

@[simp] lemma const_in_AB (v) : constAssign C_ab v ∈ supportAB := by
  simp [supportAB, constAssign]

@[simp] lemma const_in_BC (v) : constAssign C_bc v ∈ supportBC := by
  simp [supportBC, constAssign]

@[simp] lemma ac_in_AC (v) : acAssign v ∈ supportAC := by
  classical
  simp [supportAC, acAssign, a_in_ac, c_in_ac]

-- The general compatibility statements will reuse the same reasoning pattern.

-- Images of supports to singleton overlaps are all assignments (Set.univ)
private lemma img_AB_to_b_univ :
  Set.image (fun s => restrictAssign (inter_subset_left C_ab C_bc) s) supportAB = Set.univ := by
  classical
  -- Surjectivity onto the singleton-overlap assignments
  apply Set.eq_univ_iff_forall.mpr
  intro t
  refine ⟨constAssign C_ab (t ⟨b, by simp [b_mem_inter_ab_bc]⟩), ?_, ?_⟩
  · simp [supportAB, constAssign]
  · -- The restriction of a constant assignment is the constant assignment
    funext x; cases x with
    | mk i hi =>
      have hi' : i ∈ ({b} : Finset Meas) := by simpa [inter_ab_bc] using hi
      have : i = b := by simpa using (Finset.mem_singleton.mp hi')
      subst this
      simp [restrictAssign, constAssign]

private lemma img_BC_to_b_univ :
  Set.image (fun s => restrictAssign (inter_subset_right C_ab C_bc) s) supportBC = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro t
  refine ⟨constAssign C_bc (t ⟨b, by simp [b_mem_inter_ab_bc]⟩), ?_, ?_⟩
  · simp [supportBC, constAssign]
  · funext x; cases x with
    | mk i hi =>
      have hi' : i ∈ ({b} : Finset Meas) := by simpa [inter_ab_bc] using hi
      have : i = b := by simpa using (Finset.mem_singleton.mp hi')
      subst this
      simp [restrictAssign, constAssign]

private lemma img_AB_to_a_univ :
  Set.image (fun s => restrictAssign (inter_subset_left C_ab C_ac) s) supportAB = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro t
  refine ⟨constAssign C_ab (t ⟨a, by simp [a_mem_inter_ab_ac]⟩), ?_, ?_⟩
  · simp [supportAB, constAssign]
  · funext x; cases x with
    | mk i hi =>
      have hi' : i ∈ ({a} : Finset Meas) := by simpa [inter_ab_ac] using hi
      have : i = a := by simpa using (Finset.mem_singleton.mp hi')
      subst this
      simp [restrictAssign, constAssign]

private lemma img_AC_to_a_univ :
  Set.image (fun s => restrictAssign (inter_subset_right C_ab C_ac) s) supportAC = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro t
  refine ⟨acAssign (t ⟨a, by simp [a_mem_inter_ab_ac]⟩), ?_, ?_⟩
  · -- use the generic membership lemma for `acAssign`
    simpa using (ac_in_AC (t ⟨a, by simp [a_mem_inter_ab_ac]⟩))
  · funext x; cases x with
    | mk i hi =>
      have hi' : i ∈ ({a} : Finset Meas) := by simpa [inter_ab_ac] using hi
      have : i = a := by simpa using (Finset.mem_singleton.mp hi')
      subst this
      simp [restrictAssign, acAssign]

private lemma img_BC_to_c_univ :
  Set.image (fun s => restrictAssign (inter_subset_left C_bc C_ac) s) supportBC = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro t
  refine ⟨constAssign C_bc (t ⟨c, by simp [c_mem_inter_bc_ac]⟩), ?_, ?_⟩
  · simp [supportBC, constAssign]
  · funext x; cases x with
    | mk i hi =>
      have hi' : i ∈ ({c} : Finset Meas) := by simpa [inter_bc_ac] using hi
      have : i = c := by simpa using (Finset.mem_singleton.mp hi')
      subst this
      simp [restrictAssign, constAssign]

private lemma img_AC_to_c_univ :
  Set.image (fun s => restrictAssign (inter_subset_right C_bc C_ac) s) supportAC = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro t
  -- choose the AC assignment with value flipped so that on {c} it matches `t`
  refine ⟨acAssign (! (t ⟨c, by simp [c_mem_inter_bc_ac]⟩)), ?_, ?_⟩
  · simpa using (ac_in_AC (t ⟨c, by simp [c_mem_inter_bc_ac]⟩))
  · funext x; cases x with
    | mk i hi =>
      have hi' : i ∈ ({c} : Finset Meas) := by simpa [inter_bc_ac] using hi
      have : i = c := by simpa using (Finset.mem_singleton.mp hi')
      subst this
      -- At `c`, `acAssign (!v)` evaluates to `!(!v) = v`, matching `t` on the singleton
      simp [restrictAssign, acAssign]

-- Standalone support dispatcher and properties (no self-reference)
def triSupport {C : Context} (hC : C ∈ triangleCover) : Set (Assignment C) := by
  classical
  by_cases h : C = C_ab
  · cases h; exact supportAB
  · by_cases h' : C = C_bc
    · cases h'; exact supportBC
    · have : C = C_ac := by
        rcases (mem_triangleCover).1 hC with h1 | h2 | h3
        · exact (False.elim (h h1))
        · exact (False.elim (h' h2))
        · exact h3
      cases this; exact supportAC

lemma triNonempty {C : Context} (hC : C ∈ triangleCover) : (triSupport hC).Nonempty := by
  classical
  by_cases h : C = C_ab
  · cases h; simpa [triSupport] using supportAB_nonempty
  · by_cases h' : C = C_bc
    · cases h'; simpa [triSupport] using supportBC_nonempty
    · have : C = C_ac := by
        rcases (mem_triangleCover).1 hC with h1 | h2 | h3
        · exact False.elim (h h1)
        · exact False.elim (h' h2)
        · exact h3
      cases this; simpa [triSupport] using supportAC_nonempty

lemma triCompatible
  {C1 : Context} (h1 : C1 ∈ triangleCover) {C2 : Context} (h2 : C2 ∈ triangleCover) :
  let I : Context := C1 ∩ C2;
  Set.image (fun s => restrictAssign (inter_subset_left C1 C2) s) (triSupport h1) =
  Set.image (fun s => restrictAssign (inter_subset_right C1 C2) s) (triSupport h2) := by
  classical
  rcases (mem_triangleCover).1 h1 with hC1 | hC1 | hC1
  · rcases (mem_triangleCover).1 h2 with hC2 | hC2 | hC2
    · subst hC1; subst hC2
      have hfg :
        (fun s => restrictAssign (inter_subset_left C_ab C_ab) s) =
        (fun s => restrictAssign (inter_subset_right C_ab C_ab) s) := by
        funext s; simpa using restrict_inter_self_eq C_ab s
      simpa [triSupport, hfg]
    · subst hC1; subst hC2; simpa [triSupport] using (img_AB_to_b_univ.trans img_BC_to_b_univ.symm)
    · subst hC1; subst hC2; simpa [triSupport] using (img_AB_to_a_univ.trans img_AC_to_a_univ.symm)
  · rcases (mem_triangleCover).1 h2 with hC2 | hC2 | hC2
    · subst hC1; subst hC2; simpa [triSupport] using (img_BC_to_b_univ.trans img_AB_to_b_univ.symm)
    · subst hC1; subst hC2
      have hfg :
        (fun s => restrictAssign (inter_subset_left C_bc C_bc) s) =
        (fun s => restrictAssign (inter_subset_right C_bc C_bc) s) := by
        funext s; simpa using restrict_inter_self_eq C_bc s
      simpa [triSupport, hfg]
    · subst hC1; subst hC2; simpa [triSupport] using (img_BC_to_c_univ.trans img_AC_to_c_univ.symm)
  · rcases (mem_triangleCover).1 h2 with hC2 | hC2 | hC2
    · subst hC1; subst hC2; simpa [triSupport] using (img_AC_to_a_univ.trans img_AB_to_a_univ.symm)
    · subst hC1; subst hC2; simpa [triSupport] using (img_AC_to_c_univ.trans img_BC_to_c_univ.symm)
    · subst hC1; subst hC2
      have hfg :
        (fun s => restrictAssign (inter_subset_left C_ac C_ac) s) =
        (fun s => restrictAssign (inter_subset_right C_ac C_ac) s) := by
        funext s; simpa using restrict_inter_self_eq C_ac s
      simpa [triSupport, hfg]

-- Assemble the triangle empirical model
def triangleModel : EmpiricalModel triangleCover where
  support := fun {C} hC => triSupport hC
  nonempty := by intro C hC; simpa using triNonempty hC
  compatible := by
    intro C1 h1 C2 h2
    -- change goal to use `triSupport` explicitly (definitional equality with `support` field)
    change Set.image (fun s => restrictAssign (inter_subset_left C1 C2) s) (triSupport h1) =
           Set.image (fun s => restrictAssign (inter_subset_right C1 C2) s) (triSupport h2)
    simpa using (triCompatible h1 h2)

-- No global section: a=b, b=c, and a≠c are inconsistent
theorem triangle_no_global :
  NoGlobalSection X_abc triangleCover triangleModel (fun {_} h => triangle_cover_subset_X h) := by
  -- Suppose a global section exists; extract equalities and derive a contradiction.
  intro h
  rcases h with ⟨g, hg⟩
  -- From AB support: g(a)=g(b)
  have hab : (restrictAssign subset_ab_abc g) a_in_ab = (restrictAssign subset_ab_abc g) b_in_ab := by
    have hin := hg (C := C_ab) (by simp [triangleCover])
    simpa [triangleModel, supportAB] using hin
  -- From BC support: g(b)=g(c)
  have hbc : (restrictAssign subset_bc_abc g) b_in_bc = (restrictAssign subset_bc_abc g) c_in_bc := by
    have hin := hg (C := C_bc) (by simp [triangleCover])
    simpa [triangleModel, supportBC] using hin
  -- From AC support: g(a) ≠ g(c)
  have hac : (restrictAssign subset_ac_abc g) a_in_ac ≠ (restrictAssign subset_ac_abc g) c_in_ac := by
    have hin := hg (C := C_ac) (by simp [triangleCover])
    simpa [triangleModel, supportAC] using hin
  -- But hab and hbc imply equality of a and c; contradiction.
  have : (restrictAssign subset_ac_abc g) a_in_ac = (restrictAssign subset_ac_abc g) c_in_ac := by
    -- rewrite via the same underlying g values
    change g ⟨a, subset_ac_abc a_mem_ac⟩ = g ⟨c, subset_ac_abc c_mem_ac⟩
    -- transport through AB and BC equalities
    have : g ⟨a, subset_ab_abc a_mem_ab⟩ = g ⟨b, subset_ab_abc b_mem_ab⟩ := hab
    have : g ⟨a, subset_ac_abc a_mem_ac⟩ = g ⟨b, subset_bc_abc b_mem_bc⟩ := by
      simpa using hab
    have : g ⟨a, subset_ac_abc a_mem_ac⟩ = g ⟨c, subset_bc_abc c_mem_bc⟩ := by
      have hbceq : g ⟨b, subset_bc_abc b_mem_bc⟩ = g ⟨c, subset_bc_abc c_mem_bc⟩ := hbc
      exact Eq.trans this hbceq
    simpa using this
  exact hac this

end Quantum
end CryptoSheaf
end LoF
end HeytingLean
