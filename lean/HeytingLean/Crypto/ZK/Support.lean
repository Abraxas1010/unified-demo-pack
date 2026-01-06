import Mathlib.Data.Finset.Basic
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace ZK

open Classical
open Finset

/-- Assignments `a` and `a'` agree on every index contained in `dom`. -/
def AgreesOn (dom : Finset Var) (a a' : Var → ℚ) : Prop :=
  ∀ ⦃v⦄, v ∈ dom → a v = a' v

namespace AgreesOn

@[simp] lemma refl (dom : Finset Var) (a : Var → ℚ) :
    AgreesOn dom a a := by
  intro _ _; rfl

lemma symm {dom : Finset Var} {a a' : Var → ℚ}
    (h : AgreesOn dom a a') : AgreesOn dom a' a := by
  intro v hv; simpa using (h hv).symm

lemma trans {dom : Finset Var} {a b c : Var → ℚ}
    (hab : AgreesOn dom a b) (hbc : AgreesOn dom b c) :
    AgreesOn dom a c := by
  intro v hv; simpa [hab hv] using hbc hv

lemma mono {dom dom' : Finset Var} {a a' : Var → ℚ}
    (h : AgreesOn dom a a') (hSubset : dom' ⊆ dom) :
    AgreesOn dom' a a' := by
  intro v hv; exact h (hSubset hv)

lemma insert {dom : Finset Var} {v : Var} {a a' : Var → ℚ}
    (h : AgreesOn dom a a') (hv : a v = a' v) :
    AgreesOn (insert v dom) a a' := by
  intro w hw
  rcases mem_insert.mp hw with hw | hw
  · subst hw; simpa using hv
  · exact h hw

lemma erase {dom : Finset Var} {v : Var} {a a' : Var → ℚ}
    (h : AgreesOn dom a a') :
    AgreesOn (erase dom v) a a' :=
  mono h (erase_subset _ _)

end AgreesOn

namespace LinComb

/-- Variables referenced by a linear combination. -/
def support (lc : LinComb) : Finset Var :=
  lc.terms.foldr (fun term acc => insert term.1 acc) ∅

@[simp] lemma support_nil (c : ℚ) :
    support ⟨c, []⟩ = (∅ : Finset Var) := by
  simp [support]

@[simp] lemma support_cons (term : Var × ℚ) (terms : List (Var × ℚ)) (c : ℚ) :
    support ⟨c, term :: terms⟩ =
      insert term.1 (support ⟨c, terms⟩) := by
  simp [support, List.foldr_cons]

@[simp] lemma support_ofConst (c : ℚ) :
    support (LinComb.ofConst c) = (∅ : Finset Var) := by
  simp [LinComb.ofConst, support]

@[simp] lemma support_single (v : Var) (coeff : ℚ) :
    support (LinComb.single v coeff) = ({v} : Finset Var) := by
  classical
  simp [LinComb.single, support_cons, support_nil]

lemma support_terms_mem {const : ℚ} :
    ∀ (terms : List (Var × ℚ)) (v : Var),
      v ∈ support ⟨const, terms⟩ ↔ ∃ coeff, (v, coeff) ∈ terms
  | [], _ => by simp [support]
  | term :: tail, v => by
      classical
      constructor
      · intro hv
        have hv' := Finset.mem_insert.mp (by simpa [support_cons] using hv)
        cases hv' with
        | inl hVar =>
            subst hVar
            exact ⟨term.2, by simp⟩
        | inr hTail =>
            obtain ⟨coeff', hMem⟩ :=
              (support_terms_mem tail v).1 hTail
            exact ⟨coeff', List.mem_cons_of_mem _ hMem⟩
      · rintro ⟨coeff', hMem⟩
        have hCases := List.mem_cons.mp hMem
        cases hCases with
        | inl hHead =>
            have hvVar : v = term.1 := by
              simpa using congrArg Prod.fst hHead
            subst hvVar
            simp [support_cons]
        | inr hTail =>
            have hvTail :
                v ∈ support ⟨const, tail⟩ :=
              (support_terms_mem tail v).2 ⟨coeff', hTail⟩
            simp [support_cons, hvTail]

@[simp] lemma mem_support_iff {lc : LinComb} {v : Var} :
    v ∈ lc.support ↔ ∃ coeff, (v, coeff) ∈ lc.terms := by
  classical
  simpa [support] using
    (support_terms_mem (const := lc.const) lc.terms v)

lemma agree_on_term {lc : LinComb}
    {a a' : Var → ℚ}
    (h : AgreesOn lc.support a a')
    {v : Var} {coeff : ℚ} (hMem : (v, coeff) ∈ lc.terms) :
    a v = a' v := by
  classical
  have : v ∈ lc.support :=
    (mem_support_iff (lc := lc)).2 ⟨coeff, hMem⟩
  exact h this

lemma support_tail {term : Var × ℚ} {terms : List (Var × ℚ)} {c : ℚ} :
    support ⟨c, terms⟩ ⊆ support ⟨c, term :: terms⟩ := by
  classical
  intro v hv
  have : v ∈ insert term.1 (support ⟨c, terms⟩) :=
    Finset.mem_insert.mpr (Or.inr hv)
  simpa [support_cons] using this

@[simp] lemma eval_ofConst (a : Var → ℚ) (c : ℚ) :
    (LinComb.ofConst c).eval a = c := by
  simp [LinComb.ofConst, LinComb.eval]

@[simp] lemma eval_single (a : Var → ℚ) (v : Var) (coeff : ℚ) :
    (LinComb.single v coeff).eval a = coeff * a v := by
  unfold LinComb.eval
  change ([(v, coeff)]).foldl
      (fun acc term => acc + term.2 * a term.1) 0 = coeff * a v
  have h :
      ([(v, coeff)]).foldl
          (fun acc term => acc + term.2 * a term.1) 0 =
        (fun acc term => acc + term.2 * a term.1) 0 (v, coeff) := by
    simp [List.foldl_cons, List.foldl_nil]
  have h' :
      (fun acc term => acc + term.2 * a term.1) 0 (v, coeff) =
        coeff * a v := by
    change 0 + coeff * a v = coeff * a v
    simpa using Rat.zero_add (coeff * a v)
  exact h.trans h'

private lemma eval_terms_ext
    {a a' : Var → ℚ}
    (const : ℚ) :
    ∀ {terms : List (Var × ℚ)},
      AgreesOn (support ⟨const, terms⟩) a a' →
      terms.foldl
          (fun acc term => acc + term.2 * a term.1) const =
        terms.foldl
          (fun acc term => acc + term.2 * a' term.1) const
  | [], _ => by simp
  | term :: tail, h => by
      classical
      have hterm :
          a term.1 = a' term.1 :=
        agree_on_term (lc := ⟨const, term :: tail⟩)
          (a := a) (a' := a') h
          (v := term.1) (coeff := term.2) (by simp)
      have htail :
          AgreesOn (support ⟨const, tail⟩) a a' :=
        AgreesOn.mono h (support_tail (term := term) (terms := tail) (c := const))
      have ih :=
        eval_terms_ext (a := a) (a' := a')
          (const := const + term.2 * a term.1) (terms := tail) htail
      have hconst :
          const + term.2 * a term.1 =
            const + term.2 * a' term.1 := by
        simp [hterm]
      simpa [List.foldl_cons, hterm, hconst]
        using ih

lemma eval_ext {lc : LinComb} {a a' : Var → ℚ}
    (h : AgreesOn lc.support a a') :
    lc.eval a = lc.eval a' := by
  classical
  unfold LinComb.eval
  refine eval_terms_ext (a := a) (a' := a') (const := lc.const)
      (terms := lc.terms) ?_
  exact h

end LinComb

namespace Constraint

/-- Support of a single constraint. -/
def support (c : Constraint) : Finset Var :=
  c.A.support ∪ c.B.support ∪ c.C.support

lemma support_subset_left (c : Constraint) :
    c.A.support ⊆ Constraint.support c := by
  intro v hv
  dsimp [support]
  apply Finset.mem_union.mpr
  refine Or.inl ?_
  apply Finset.mem_union.mpr
  exact Or.inl hv

lemma support_subset_middle (c : Constraint) :
    c.B.support ⊆ Constraint.support c := by
  intro v hv
  dsimp [support]
  apply Finset.mem_union.mpr
  refine Or.inl ?_
  apply Finset.mem_union.mpr
  exact Or.inr hv

lemma support_subset_right (c : Constraint) :
    c.C.support ⊆ Constraint.support c := by
  intro v hv
  dsimp [support]
  apply Finset.mem_union.mpr
  exact Or.inr hv

lemma satisfied_ext {c : Constraint} {a a' : Var → ℚ}
    (hA : AgreesOn c.A.support a a')
    (hB : AgreesOn c.B.support a a')
    (hC : AgreesOn c.C.support a a') :
    Constraint.satisfied a c ↔ Constraint.satisfied a' c := by
  unfold Constraint.satisfied
  constructor <;> intro h
  · simpa [LinComb.eval_ext (lc := c.A) hA,
      LinComb.eval_ext (lc := c.B) hB,
      LinComb.eval_ext (lc := c.C) hC] using h
  · simpa [LinComb.eval_ext (lc := c.A) (AgreesOn.symm hA),
      LinComb.eval_ext (lc := c.B) (AgreesOn.symm hB),
      LinComb.eval_ext (lc := c.C) (AgreesOn.symm hC)] using h

end Constraint

namespace System

/-- Canonical wrapper that keeps `System.satisfied` in a stable propositional form. -/
def satisfied_cons (a : Var → ℚ) (sys : System) : Prop :=
  System.satisfied a sys

@[simp] lemma satisfied_iff_cons {a : Var → ℚ} {sys : System} :
    System.satisfied a sys ↔ System.satisfied_cons a sys :=
  Iff.rfl

private def supportList : List Constraint → Finset Var
  | [] => ∅
  | c :: cs => supportList cs ∪ Constraint.support c

/-- Support of all constraints stored in the system. -/
def support (sys : System) : Finset Var :=
  supportList sys.constraints

@[simp] lemma support_nil :
    support ⟨[]⟩ = (∅ : Finset Var) := rfl

@[simp] lemma support_cons (c : Constraint) (cs : List Constraint) :
    support ⟨c :: cs⟩ =
      support ⟨cs⟩ ∪ Constraint.support c := rfl

lemma constraint_support_subset {sys : System}
    {c : Constraint} (hc : c ∈ sys.constraints) :
    Constraint.support c ⊆ support sys := by
  classical
  revert c
  cases sys with
  | mk constraints =>
      induction constraints with
      | nil =>
          intro c hc
          cases hc
      | cons head tail ih =>
          intro c hc
          have hc' := List.mem_cons.mp hc
          cases hc' with
          | inl hEq =>
              subst hEq
              intro v hv
              exact Finset.mem_union.mpr (Or.inr hv)
          | inr hMem =>
              intro v hv
              have hvTail : v ∈ support ⟨tail⟩ :=
                (ih hMem) hv
              exact Finset.mem_union.mpr (Or.inl hvTail)

lemma support_perm {cs cs' : List Constraint} (h : List.Perm cs cs') :
    support ⟨cs⟩ = support ⟨cs'⟩ := by
  classical
  refine List.Perm.rec ?h₁ ?h₂ ?h₃ ?h₄ h
  · simp [support]
  · intro x l₁ l₂ hPerm ih
    simp [support_cons, ih]
  · intro x y l
    simp [support_cons, Finset.union_left_comm, Finset.union_comm]
  · intro l₁ l₂ l₃ h₁ h₂ ih₁ ih₂
    exact ih₁.trans ih₂

lemma support_reverse (cs : List Constraint) :
    support ⟨cs.reverse⟩ = support ⟨cs⟩ :=
  support_perm <|
    (List.perm_reverse).1 (List.Perm.refl cs.reverse)

lemma satisfied_ext {sys : System}
    {a a' : Var → ℚ} {dom : Finset Var}
    (hSupp : support sys ⊆ dom)
    (hAgree : AgreesOn dom a a') :
    System.satisfied a sys ↔ System.satisfied a' sys := by
  constructor <;> intro h c hc
  · have hSub : Constraint.support c ⊆ dom :=
      subset_trans (constraint_support_subset (sys := sys) hc) hSupp
    have hA :
        AgreesOn c.A.support a a' :=
      AgreesOn.mono hAgree
        (subset_trans (Constraint.support_subset_left c) hSub)
    have hB :
        AgreesOn c.B.support a a' :=
      AgreesOn.mono hAgree
        (subset_trans (Constraint.support_subset_middle c) hSub)
    have hC :
        AgreesOn c.C.support a a' :=
      AgreesOn.mono hAgree
        (subset_trans (Constraint.support_subset_right c) hSub)
    have := (Constraint.satisfied_ext (c := c) hA hB hC).1 (h hc)
    simpa using this
  · have hSub : Constraint.support c ⊆ dom :=
      subset_trans (constraint_support_subset (sys := sys) hc) hSupp
    have hA :
        AgreesOn c.A.support a' a :=
      AgreesOn.mono (AgreesOn.symm hAgree)
        (subset_trans (Constraint.support_subset_left c) hSub)
    have hB :
        AgreesOn c.B.support a' a :=
      AgreesOn.mono (AgreesOn.symm hAgree)
        (subset_trans (Constraint.support_subset_middle c) hSub)
    have hC :
        AgreesOn c.C.support a' a :=
      AgreesOn.mono (AgreesOn.symm hAgree)
        (subset_trans (Constraint.support_subset_right c) hSub)
    have := (Constraint.satisfied_ext (c := c) hA hB hC).1 (h hc)
    simpa using this

lemma satisfied_of_agreesOn_support {sys : System}
    {a a' : Var → ℚ}
    (hAgree : AgreesOn (support sys) a a') :
    System.satisfied a sys ↔ System.satisfied a' sys :=
  satisfied_ext (sys := sys) (dom := support sys)
    (hSupp := by intro _ hv; simpa using hv) (hAgree := hAgree)

lemma satisfied_cons_cons {a : Var → ℚ} {c : Constraint} {sys : System} :
    System.satisfied a { sys with constraints := c :: sys.constraints } ↔
      Constraint.satisfied a c ∧ System.satisfied a sys := by
  classical
  unfold System.satisfied
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact h (by simp [List.mem_cons])
    · intro d hd
      exact h (by simp [List.mem_cons, hd])
  · rintro ⟨hHead, hTail⟩ d hd
    have hd' : d = c ∨ d ∈ sys.constraints :=
      List.mem_cons.mp (by simpa using hd)
    cases hd' with
    | inl hdc =>
        subst hdc
        simpa using hHead
    | inr hdTail =>
        simpa using hTail hdTail

lemma satisfied_of_perm {assign : Var → ℚ}
    {cs cs' : List Constraint} (h : List.Perm cs cs') :
    System.satisfied assign { constraints := cs } ↔
      System.satisfied assign { constraints := cs' } := by
  classical
  constructor <;> intro hSat c hc
  · have hc' : c ∈ cs := (List.Perm.mem_iff h).mpr hc
    exact hSat hc'
  · have hc' : c ∈ cs' := (List.Perm.mem_iff h.symm).mpr hc
    exact hSat hc'

lemma satisfied_reverse {assign : Var → ℚ} {cs : List Constraint} :
    System.satisfied assign { constraints := cs.reverse } ↔
      System.satisfied assign { constraints := cs } :=
  satisfied_of_perm <|
    (List.perm_reverse).1 (List.Perm.refl cs.reverse)

end System

end ZK
end Crypto
end HeytingLean
