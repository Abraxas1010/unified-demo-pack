import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.VM
import HeytingLean.Crypto.Compile
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.BoolArith
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Support

open scoped BigOperators

namespace HeytingLean
namespace Crypto
namespace ZK
namespace R1CSBool

open BoolLens
open Finset

/-- Builder state used while translating a boolean trace to R1CS. -/
structure Builder where
  nextVar : Var := 0
  assign : Var → ℚ := fun _ => 0
  constraints : List Constraint := []

namespace Builder

/-- Allocate a fresh variable with the provided witness value. -/
def fresh (st : Builder) (value : ℚ) : Builder × Var :=
  let idx := st.nextVar
  let assign' : Var → ℚ := fun j => if j = idx then value else st.assign j
  ({ nextVar := idx + 1, assign := assign', constraints := st.constraints }, idx)

/-- Append a constraint to the builder. -/
def addConstraint (st : Builder) (c : Constraint) : Builder :=
  { st with constraints := c :: st.constraints }

end Builder

/-- Booleanity constraint ensuring `v ∈ {0,1}`. -/
def boolConstraint (v : Var) : Constraint :=
  { A := LinComb.single v 1
    B := ⟨-1, [(v, 1)]⟩
    C := LinComb.ofConst 0 }

/-- Support of the booleanity constraint is the singleton `{v}`. -/
@[simp] lemma boolConstraint_support (v : Var) :
    Constraint.support (boolConstraint v) = ({v} : Finset Var) := by
  classical
  simp [Constraint.support, boolConstraint]

/-- Booleanity constraint evaluates to `a v * (a v - 1) = 0`. -/
@[simp] lemma boolConstraint_satisfied (assign : Var → ℚ) (v : Var) :
    Constraint.satisfied assign (boolConstraint v) ↔
      assign v * (assign v - 1) = 0 := by
  classical
  have hB :
      (⟨-1, [(v, 1)]⟩ : LinComb).eval assign = assign v - 1 := by
    simp [LinComb.eval, sub_eq_add_neg, add_comm]
  simp [Constraint.satisfied, boolConstraint, LinComb.eval_single,
    LinComb.eval_ofConst, hB, sub_eq_add_neg]

/-- Constraint enforcing `v = constant`. -/
def eqConstConstraint (v : Var) (value : ℚ) : Constraint :=
  { A := LinComb.single v 1
    B := LinComb.ofConst 1
    C := LinComb.ofConst value }

/-- Support of the equality-to-constant constraint is `{v}`. -/
@[simp] lemma eqConstConstraint_support (v : Var) (value : ℚ) :
    Constraint.support (eqConstConstraint v value) = ({v} : Finset Var) := by
  classical
  simp [Constraint.support, eqConstConstraint]

/-- Satisfying `eqConstConstraint` is definitionally the equality `assign v = value`. -/
@[simp] lemma eqConstConstraint_satisfied (assign : Var → ℚ)
    (v : Var) (value : ℚ) :
    Constraint.satisfied assign (eqConstConstraint v value) ↔
      assign v = value := by
  classical
  simp [Constraint.satisfied, eqConstConstraint]

lemma eqConstConstraint_head_satisfied
    (assign : Var → ℚ) (v : Var) (value : ℚ) :
    assign v = value →
      Constraint.satisfied assign (eqConstConstraint v value) := by
  intro h
  simpa using
    ((eqConstConstraint_satisfied
          (assign := assign) (v := v) (value := value)).2 h)

@[simp] lemma boolToRat_mul_self_sub_one (b : Bool) :
    boolToRat b * (boolToRat b - 1) = 0 := by
  exact ZK.boolToRat_sq_sub b

/-- Constraint enforcing `lhs = rhs` using a single multiplicative slot. -/
def eqConstraint (lhs rhs : LinComb) : Constraint :=
  { A := lhs, B := LinComb.ofConst 1, C := rhs }

/-- Result of compiling a Boolean form to R1CS. -/
structure Compiled where
  system : System
  assignment : Var → ℚ
  output : Var

private def recordBoolean (builder : Builder) (var : Var) : Builder :=
  Builder.addConstraint builder (boolConstraint var)

private def pushConst (builder : Builder) (value : ℚ) :
    Builder × Var := by
  classical
  let (builder', v) := Builder.fresh builder value
  let builder'' := Builder.addConstraint builder' (eqConstConstraint v value)
  exact (recordBoolean builder'' v, v)

/-- Relation connecting a Boolean stack with its assigned R1CS variables. -/
def Matches (builder : Builder) (stack : Stack) (vars : List Var) : Prop :=
  List.Forall₂ (fun b v => boolToRat b = builder.assign v) stack vars

/-- Every variable stored on the stack is strictly below the current `nextVar`. -/
def Bounded (builder : Builder) (vars : List Var) : Prop :=
  ∀ v, v ∈ vars → v < builder.nextVar

def Builder.system (builder : Builder) : System :=
  { constraints := builder.constraints }

def SupportOK (builder : Builder) : Prop :=
  System.support (Builder.system builder) ⊆ Finset.range builder.nextVar

def StrongInvariant (builder : Builder) (stack : Stack) (vars : List Var) : Prop :=
  Matches builder stack vars ∧
    Bounded builder vars ∧
    SupportOK builder ∧
    System.satisfied builder.assign (Builder.system builder)

namespace StrongInvariant

lemma matches_ {builder : Builder} {stack : Stack} {vars : List Var}
    (h : StrongInvariant builder stack vars) : Matches builder stack vars :=
  h.1

lemma bounded_ {builder : Builder} {stack : Stack} {vars : List Var}
    (h : StrongInvariant builder stack vars) : Bounded builder vars :=
  h.2.1

lemma support_ {builder : Builder} {stack : Stack} {vars : List Var}
    (h : StrongInvariant builder stack vars) : SupportOK builder :=
  h.2.2.1

lemma satisfied_ {builder : Builder} {stack : Stack} {vars : List Var}
    (h : StrongInvariant builder stack vars) :
    System.satisfied builder.assign (Builder.system builder) :=
  h.2.2.2

lemma toInvariant {builder : Builder} {stack : Stack} {vars : List Var}
    (h : StrongInvariant builder stack vars) :
    Matches builder stack vars ∧ Bounded builder vars :=
  ⟨matches_ h, bounded_ h⟩

end StrongInvariant

@[simp] lemma support_empty_iff_false (v : Var) :
    v ∈ System.support (Builder.system ({} : Builder)) ↔ False := by
  simp [Builder.system, System.support_nil]

@[simp] lemma strongInvariant_empty :
    StrongInvariant ({} : Builder) [] [] := by
  classical
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · simp [Matches]
  · intro v hv; cases hv
  · intro v hv
    have hFalse : False := (support_empty_iff_false v).1 hv
    exact hFalse.elim
  · intro c hc
    cases hc

namespace StrongInvariant

lemma support_reverse_subset {builder : Builder} {stack : Stack}
    {vars : List Var} (h : StrongInvariant builder stack vars) :
    System.support { constraints := builder.constraints.reverse } ⊆
      Finset.range builder.nextVar := by
  intro v hv
  let hEq :
      System.support { constraints := builder.constraints.reverse } =
        System.support { constraints := builder.constraints } :=
    System.support_reverse (cs := builder.constraints)
  have hv' :
      v ∈ System.support { constraints := builder.constraints } := by
    simpa [hEq] using hv
  have hvOrig :
      v ∈ System.support (Builder.system builder) := by
    simpa [Builder.system] using hv'
  exact (support_ h) hvOrig

end StrongInvariant

private lemma range_subset_succ (n : ℕ) :
    Finset.range n ⊆ Finset.range (n + 1) := by
  intro v hv
  have hvlt : v < n := Finset.mem_range.mp hv
  exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hvlt)

private lemma singleton_subset_range {n v : ℕ} (hv : v < n) :
    ({v} : Finset Var) ⊆ Finset.range n := by
  intro w hw
  have hw' : w = v := Finset.mem_singleton.mp hw
  subst hw'
  exact Finset.mem_range.mpr hv

lemma singleton_subset_range_of_lt {n v : ℕ} (hv : v < n) :
    ({v} : Finset Var) ⊆ Finset.range n :=
  singleton_subset_range (n := n) (v := v) hv

lemma mulConstraint_support_subset
    {n vx vy vz : Nat}
    (hx : vx < n) (hy : vy < n) (hz : vz < n) :
    Constraint.support
        { A := LinComb.single vx 1
          B := LinComb.single vy 1
          C := LinComb.single vz 1 } ⊆ Finset.range n := by
  classical
  intro w hw
  have hw' :
      w = vx ∨ w = vy ∨ w = vz := by
    simpa [Constraint.support, LinComb.support_single,
      Finset.mem_union, Finset.mem_singleton,
      or_left_comm, or_assoc, or_comm] using hw
  rcases hw' with h | h | h
  · subst h; exact Finset.mem_range.mpr hx
  · subst h; exact Finset.mem_range.mpr hy
  · subst h; exact Finset.mem_range.mpr hz

lemma four_var_support_subset
    {n vz vx vy vmul : Nat}
    (hz : vz < n) (hx : vx < n) (hy : vy < n) (hm : vmul < n) :
    ({vz} ∪ {vx} ∪ {vy} ∪ {vmul} : Finset Var) ⊆ Finset.range n := by
  classical
  intro w hw
  have hw' :
      w = vz ∨ w = vx ∨ w = vy ∨ w = vmul := by
    simpa [Finset.mem_union, Finset.mem_singleton,
      or_left_comm, or_comm, or_assoc] using hw
  rcases hw' with h | h | h | h
  · subst h; exact Finset.mem_range.mpr hz
  · subst h; exact Finset.mem_range.mpr hx
  · subst h; exact Finset.mem_range.mpr hy
  · subst h; exact Finset.mem_range.mpr hm

lemma boolean_mul_closed {F} [Semiring F]
    {x y : F} :
    (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) →
      (x * y = 0 ∨ x * y = 1) := by
  intro hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

lemma boolean_or_closed {F} [Ring F]
    {x y : F} :
    (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) →
      (x + y - x * y = 0 ∨ x + y - x * y = 1) := by
  intro hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

lemma boolean_imp_closed {F} [Ring F]
    {x y : F} :
    (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) →
      (1 - x + x * y = 0 ∨ 1 - x + x * y = 1) := by
  intro hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

lemma mul_head_satisfied_of_eq
    (a : Var → ℚ) (vx vy vz : Var)
    (h : a vx * a vy = a vz) :
    Constraint.satisfied a
      { A := LinComb.single vx 1
        B := LinComb.single vy 1
        C := LinComb.single vz 1 } := by
  classical
  simp [Constraint.satisfied, LinComb.eval_single, h]

lemma eqConstraint_head_satisfied_of_eval
    (a : Var → ℚ) (lhs rhs : LinComb)
    (h : lhs.eval a = rhs.eval a) :
    Constraint.satisfied a (eqConstraint lhs rhs) := by
  classical
  simp [Constraint.satisfied, eqConstraint, LinComb.eval_ofConst, h]

def linhead_or (vz vx vy vmul : Var) : LinComb :=
  ⟨0, [(vz, 1), (vmul, 1), (vx, -1), (vy, -1)]⟩

lemma linhead_or_support
    (vz vx vy vmul : Var) :
    (linhead_or vz vx vy vmul).support ⊆
      ({vz} ∪ {vx} ∪ {vy} ∪ {vmul} : Finset Var) := by
  classical
  intro v hv
  have hvCases :
      v = vz ∨ v = vmul ∨ v = vx ∨ v = vy := by
    simpa [linhead_or, LinComb.support_cons, LinComb.support_nil,
      Finset.mem_insert, Finset.mem_singleton] using hv
  have hvGoal :
      v ∈ ({vz} ∪ {vx} ∪ {vy} ∪ {vmul} : Finset Var) := by
    rcases hvCases with hvz | hvRest
    · subst hvz
      simp
    · rcases hvRest with hMul | hvRest
      · subst hMul
        simp
      · rcases hvRest with hvx | hvy
        · subst hvx
          simp
        · subst hvy
          simp
  exact hvGoal

lemma linhead_or_eval
    {ρ : Var → ℚ} {vx vy vmul vz : Var}
    (Hx : ρ vmul = ρ vx * ρ vy)
    (Hz : ρ vz = ρ vx + ρ vy - ρ vx * ρ vy) :
    (linhead_or vz vx vy vmul).eval ρ = 0 := by
  simpa [linhead_or] using
    (_root_.HeytingLean.Crypto.ZK.lin_eval_or
      (ρ := ρ) (vx := vx) (vy := vy) (vmul := vmul) (vz := vz) Hx Hz)

lemma head_satisfied_or
    (a : Var → ℚ) {vx vy vmul vz : Var}
    (Hx : a vmul = a vx * a vy)
    (Hz : a vz = a vx + a vy - a vx * a vy) :
    Constraint.satisfied a
      (eqConstraint (linhead_or vz vx vy vmul) (LinComb.ofConst 0)) := by
  have hEval :
      (linhead_or vz vx vy vmul).eval a =
        (LinComb.ofConst 0).eval a := by
    simpa [LinComb.eval_ofConst] using
      linhead_or_eval (ρ := a) (vx := vx) (vy := vy)
        (vmul := vmul) (vz := vz) Hx Hz
  exact eqConstraint_head_satisfied_of_eval
    (a := a) (lhs := linhead_or vz vx vy vmul)
    (rhs := LinComb.ofConst 0) hEval

def linhead_imp (vz _vx vy vmul : Var) : LinComb :=
  ⟨-1, [(vz, 1), (vy, 1), (vmul, -1)]⟩

lemma linhead_imp_support
    (vz _vx vy vmul : Var) :
    (linhead_imp vz vx vy vmul).support ⊆
      ({vz} ∪ {vx} ∪ {vy} ∪ {vmul} : Finset Var) := by
  classical
  intro v hv
  have hvCases :
      v = vz ∨ v = vy ∨ v = vmul := by
    simpa [linhead_imp, LinComb.support_cons, LinComb.support_nil,
      Finset.mem_insert, Finset.mem_singleton] using hv
  have hvGoal :
      v ∈ ({vz} ∪ {vx} ∪ {vy} ∪ {vmul} : Finset Var) := by
    rcases hvCases with hvz | hvRest
    · subst hvz
      simp
    · rcases hvRest with hvy | hvmul
      · subst hvy
        simp
      · subst hvmul
        simp
  exact hvGoal

lemma linhead_imp_eval
    {ρ : Var → ℚ} {vx vy vmul vz : Var}
    (Hx : ρ vmul = ρ vx * ρ vy)
    (Hz : ρ vz = 1 - ρ vy + ρ vy * ρ vx) :
    (linhead_imp vz vx vy vmul).eval ρ = 0 := by
  simpa [linhead_imp] using
    (_root_.HeytingLean.Crypto.ZK.lin_eval_imp
      (ρ := ρ) (vx := vx) (vy := vy) (vmul := vmul) (vz := vz) Hx Hz)

lemma head_satisfied_imp
    (a : Var → ℚ) {vx vy vmul vz : Var}
    (Hx : a vmul = a vx * a vy)
    (Hz : a vz = 1 - a vy + a vy * a vx) :
    Constraint.satisfied a
      (eqConstraint (linhead_imp vz vx vy vmul) (LinComb.ofConst 0)) := by
  have hEval :
      (linhead_imp vz vx vy vmul).eval a =
        (LinComb.ofConst 0).eval a := by
    simpa [LinComb.eval_ofConst] using
      linhead_imp_eval (ρ := a) (vx := vx) (vy := vy)
        (vmul := vmul) (vz := vz) Hx Hz
  exact eqConstraint_head_satisfied_of_eval
    (a := a) (lhs := linhead_imp vz vx vy vmul)
    (rhs := LinComb.ofConst 0) hEval

namespace Builder

@[simp] lemma system_constraints (st : Builder) :
    (Builder.system st).constraints = st.constraints := rfl

@[simp] lemma system_fresh (st : Builder) (value : ℚ) :
    Builder.system (fresh st value).1 = Builder.system st := rfl

@[simp] lemma system_addConstraint (st : Builder) (c : Constraint) :
    Builder.system (addConstraint st c) =
      { (Builder.system st) with constraints := c :: (Builder.system st).constraints } := rfl

@[simp] lemma system_recordBoolean (st : Builder) (v : Var) :
    Builder.system (recordBoolean st v) =
      { (Builder.system st) with constraints := boolConstraint v :: (Builder.system st).constraints } := rfl

@[simp] lemma addConstraint_assign (st : Builder) (c : Constraint) :
    (addConstraint st c).assign = st.assign := rfl

@[simp] lemma addConstraint_nextVar (st : Builder) (c : Constraint) :
    (addConstraint st c).nextVar = st.nextVar := rfl

@[simp] lemma recordBoolean_assign (st : Builder) (v : Var) :
    (recordBoolean st v).assign = st.assign := by
  unfold recordBoolean
  simp

@[simp] lemma recordBoolean_nextVar (st : Builder) (v : Var) :
    (recordBoolean st v).nextVar = st.nextVar := by
  unfold recordBoolean
  simp

@[simp] lemma fresh_nextVar (st : Builder) (value : ℚ) :
    (fresh st value).1.nextVar = st.nextVar + 1 := by
  simp [fresh]

@[simp] lemma fresh_assign_self (st : Builder) (value : ℚ) :
    (fresh st value).1.assign (fresh st value).2 = value := by
  classical
  dsimp [fresh]
  simp

@[simp] lemma fresh_assign_lt {st : Builder} {value : ℚ} {w : Var}
    (hw : w < st.nextVar) :
    (fresh st value).1.assign w = st.assign w := by
  classical
  dsimp [fresh]
  have : w ≠ st.nextVar := Nat.ne_of_lt hw
  simp [this]

@[simp] lemma fresh_snd (st : Builder) (value : ℚ) :
    (fresh st value).2 = st.nextVar := rfl

lemma fresh_preserve_bounded {st : Builder} {value : ℚ} {vars : List Var}
    (h : Bounded st vars) :
    Bounded (fresh st value).1 vars := by
  classical
  refine fun v hv => ?_
  have hvlt := h v hv
  have : v < st.nextVar + 1 := Nat.lt_succ_of_lt hvlt
  simpa [fresh] using this

lemma fresh_preserve_support {st : Builder} {value : ℚ}
    (h : SupportOK st) :
    SupportOK (fresh st value).1 := by
  intro v hv
  have hvOld : v ∈ System.support (Builder.system st) := by
    simpa using hv
  have hvRange : v ∈ Finset.range st.nextVar := h hvOld
  have hvRangeSucc : v ∈ Finset.range (st.nextVar + 1) :=
    range_subset_succ st.nextVar hvRange
  simpa [fresh] using hvRangeSucc

lemma fresh_agreesOn_range (st : Builder) (value : ℚ) :
    AgreesOn (Finset.range st.nextVar) st.assign (fresh st value).1.assign := by
  intro v hv
  have hvlt : v < st.nextVar := Finset.mem_range.mp hv
  have := fresh_assign_lt (st := st) (value := value) (w := v) (hw := hvlt)
  simpa using this.symm

lemma fresh_preserve_satisfied_mem {st : Builder} {value : ℚ}
    (hSupport : SupportOK st)
    (hSat : System.satisfied st.assign (Builder.system st)) :
    System.satisfied (fresh st value).1.assign
        (Builder.system (fresh st value).1) := by
  classical
  intro c hc
  have hSatOld :
      System.satisfied (fresh st value).1.assign (Builder.system st) :=
    (System.satisfied_ext
        (sys := Builder.system st)
        (a := st.assign)
        (a' := (fresh st value).1.assign)
        (dom := Finset.range st.nextVar)
        (hSupp := hSupport)
        (hAgree := fresh_agreesOn_range st value)).1 hSat
  have hcOld : c ∈ (Builder.system st).constraints := by
    simpa using hc
  have := hSatOld hcOld
  simpa using this

lemma addConstraint_preserve_support {st : Builder} {c : Constraint}
    (hSupport : SupportOK st)
    (hc : Constraint.support c ⊆ Finset.range st.nextVar) :
    SupportOK (addConstraint st c) := by
  classical
  intro v hv
  have hvUnion :
      v ∈ System.support (Builder.system st) ∪ Constraint.support c := by
    simpa [Builder.system_addConstraint] using hv
  have hCases := Finset.mem_union.mp hvUnion
  cases hCases with
  | inl hvOld =>
      have := hSupport hvOld
      simpa [Builder.addConstraint_nextVar] using this
  | inr hvNew =>
      have := hc hvNew
      simpa [Builder.addConstraint_nextVar] using this

lemma addConstraint_preserve_satisfied_mem {st : Builder} {c : Constraint}
    (hSat : System.satisfied st.assign (Builder.system st))
    (hc : Constraint.satisfied st.assign c) :
    System.satisfied (addConstraint st c).assign
        (Builder.system (addConstraint st c)) := by
  intro d hd
  have hdCons : d = c ∨ d ∈ st.constraints := by
    simpa [Builder.system_addConstraint] using hd
  cases hdCons with
  | inl hdc =>
      subst hdc
      simpa [Builder.addConstraint_assign] using hc
  | inr hdOld =>
      have := hSat hdOld
      simpa [Builder.addConstraint_assign] using this

end Builder

lemma addConstraint_preserve_matches {builder : Builder} {stack vars}
    (h : Matches builder stack vars) (c : Constraint) :
    Matches (Builder.addConstraint builder c) stack vars := by
  simpa [Matches] using h

lemma addConstraint_preserve_bounded {builder : Builder} {vars : List Var}
    (h : Bounded builder vars) (c : Constraint) :
    Bounded (Builder.addConstraint builder c) vars := by
  simpa [Bounded] using h

lemma recordBoolean_preserve_matches {builder : Builder} {stack vars} (v : Var)
    (h : Matches builder stack vars) :
    Matches (recordBoolean builder v) stack vars := by
  unfold recordBoolean
  simpa [Matches] using h

lemma recordBoolean_preserve_bounded {builder : Builder} {vars : List Var} (v : Var)
    (h : Bounded builder vars) :
    Bounded (recordBoolean builder v) vars := by
  unfold recordBoolean
  simpa [Bounded] using h

lemma recordBoolean_preserve_support {builder : Builder} {v : Var}
    (hSupport : SupportOK builder) (hv : v < builder.nextVar) :
    SupportOK (recordBoolean builder v) := by
  classical
  have hSubset :
      Constraint.support (boolConstraint v) ⊆ Finset.range builder.nextVar := by
    intro w hw
    have hw' : w = v := by
      simpa [boolConstraint_support] using hw
    subst hw'
    exact Finset.mem_range.mpr hv
  have :=
    Builder.addConstraint_preserve_support
      (st := builder) (c := boolConstraint v) hSupport hSubset
  simpa [recordBoolean, Builder.system_recordBoolean]
    using this

lemma recordBoolean_preserve_satisfied_mem {builder : Builder} {v : Var}
    (hSat : System.satisfied builder.assign (Builder.system builder))
    (hv : Constraint.satisfied builder.assign (boolConstraint v)) :
    System.satisfied (recordBoolean builder v).assign
        (Builder.system (recordBoolean builder v)) := by
  classical
  unfold System.satisfied at hSat ⊢
  intro c hc
  have hc' : c = boolConstraint v ∨ c ∈ builder.constraints := by
    simpa [recordBoolean, Builder.system_recordBoolean] using hc
  -- `recordBoolean` does not change the assignment except for adding the constraint.
  have hAssign :
      (recordBoolean builder v).assign = builder.assign := by
    simp [recordBoolean]
  cases hc' with
  | inl hEq =>
      subst hEq
      -- Constraint satisfied by assumption `hv`.
      simpa [hAssign] using hv
  | inr hMem =>
      have := hSat hMem
      simpa [hAssign] using this

namespace BuilderPreserve

lemma fresh_agreesOn_support {b : Builder} {val : ℚ}
    (hOK : SupportOK b) :
    ∀ v ∈ System.support (Builder.system b),
      b.assign v = (Builder.fresh b val).1.assign v := by
  intro v hv
  have hvRange : v ∈ Finset.range b.nextVar := hOK hv
  have hvlt : v < b.nextVar := Finset.mem_range.mp hvRange
  have hEq := Builder.fresh_assign_lt (st := b) (value := val) (w := v) (hw := hvlt)
  simpa using hEq.symm

lemma fresh_preserve_satisfied {b : Builder} {val : ℚ}
    (hOK : SupportOK b)
    (hSat : System.satisfied b.assign (Builder.system b)) :
    System.satisfied (Builder.fresh b val).1.assign
        (Builder.system (Builder.fresh b val).1) :=
  Builder.fresh_preserve_satisfied_mem (st := b) (value := val) hOK hSat

lemma addConstraint_preserve_satisfied {b : Builder} {c : Constraint}
    (hTail : System.satisfied b.assign (Builder.system b))
    (hHead : Constraint.satisfied b.assign c) :
    System.satisfied (Builder.addConstraint b c).assign
        (Builder.system (Builder.addConstraint b c)) :=
  Builder.addConstraint_preserve_satisfied_mem
    (st := b) (c := c) hTail hHead

lemma recordBoolean_preserve_satisfied {b : Builder} {v : Var}
    (hSat : System.satisfied b.assign (Builder.system b))
    (hv : Constraint.satisfied b.assign (boolConstraint v)) :
    System.satisfied (recordBoolean b v).assign
        (Builder.system (recordBoolean b v)) :=
  _root_.HeytingLean.Crypto.ZK.R1CSBool.recordBoolean_preserve_satisfied_mem
    (builder := b) (v := v) hSat hv

end BuilderPreserve

@[simp] lemma matches_nil (builder : Builder) :
    Matches builder [] [] := List.Forall₂.nil

lemma matches_cons_head {builder : Builder} {b : Bool} {stack : Stack}
    {v : Var} {vars : List Var}
    (h : Matches builder (b :: stack) (v :: vars)) :
    boolToRat b = builder.assign v := by
  cases h with
  | cons hHead _ => simpa using hHead

lemma matches_cons_tail {builder : Builder} {b : Bool} {stack : Stack}
    {v : Var} {vars : List Var}
    (h : Matches builder (b :: stack) (v :: vars)) :
    Matches builder stack vars := by
  cases h with
  | cons _ hTail => simpa using hTail

lemma matches_tail_tail {builder : Builder} {b₁ b₂ : Bool} {stack : Stack}
    {v₁ v₂ : Var} {vars : List Var}
    (h : Matches builder (b₁ :: b₂ :: stack) (v₁ :: v₂ :: vars)) :
    Matches builder stack vars := by
  have hTail₁ :=
    matches_cons_tail (builder := builder) (b := b₁)
      (stack := b₂ :: stack) (v := v₁) (vars := v₂ :: vars) h
  exact matches_cons_tail (builder := builder) (b := b₂)
      (stack := stack) (v := v₂) (vars := vars) hTail₁

lemma matches_length_eq {builder : Builder} {stack : Stack} {vars : List Var}
    (h : Matches builder stack vars) :
    stack.length = vars.length := by
  induction h with
  | nil => simp
  | cons _ _ ih => simp [ih]

lemma matches_fresh_preserve {builder : Builder} {stack : Stack}
    {vars : List Var} {value : ℚ}
    (hM : Matches builder stack vars)
    (hB : Bounded builder vars) :
    Matches (Builder.fresh builder value).1 stack vars := by
  classical
  revert hB
  induction hM with
  | nil => intro; simp [Matches]
  | @cons b v stack vars hHead hTail ih =>
      intro hB
      have hvlt : v < builder.nextVar := hB v (by simp)
      have hBtail : Bounded builder vars := by
        intro w hw; exact hB w (by simp [hw])
      have hTail' := ih hBtail
      have hAssign := Builder.fresh_assign_lt (st := builder)
        (value := value) (w := v) (hw := hvlt)
      refine List.Forall₂.cons ?_ hTail'
      simpa [hAssign] using hHead

lemma Bounded.tail {builder : Builder} {v : Var} {vars : List Var}
    (h : Bounded builder (v :: vars)) :
    Bounded builder vars := by
  intro w hw
  exact h w (by simp [hw])

lemma Bounded.tail_tail {builder : Builder} {v₁ v₂ : Var} {vars : List Var}
    (h : Bounded builder (v₁ :: v₂ :: vars)) :
    Bounded builder vars :=
  Bounded.tail
    (builder := builder)
    (v := v₂) (vars := vars)
    (Bounded.tail (builder := builder)
      (v := v₁) (vars := v₂ :: vars) h)

/-- Convenience invariant bundling matches, bounds, and stack length. -/
def Invariant (builder : Builder) (stack : Stack) (vars : List Var) : Prop :=
  Matches builder stack vars ∧ Bounded builder vars ∧ stack.length = vars.length

namespace Invariant

lemma tail {builder : Builder} {stack : Stack} {vars : List Var}
    {b : Bool} {v : Var}
    (h : Invariant builder (b :: stack) (v :: vars)) :
    Invariant builder stack vars :=
  ⟨matches_cons_tail h.1, Bounded.tail h.2.1,
    by
      have := h.2.2
      simp [List.length_cons] at this
      exact this⟩

lemma tail₂ {builder : Builder} {stack : Stack} {vars : List Var}
    {b₁ b₂ : Bool} {v₁ v₂ : Var}
    (h : Invariant builder (b₁ :: b₂ :: stack) (v₁ :: v₂ :: vars)) :
    Invariant builder stack vars :=
  tail (builder := builder)
    (stack := stack) (vars := vars) (b := b₂) (v := v₂)
    (tail (builder := builder)
      (stack := b₂ :: stack) (vars := v₂ :: vars)
      (b := b₁) (v := v₁) h)

end Invariant

lemma pushConst_invariant {builder : Builder} {stack : Stack}
    {vars : List Var} {value : ℚ} {b : Bool}
    (hInv : Invariant builder stack vars)
    (hvalue : value = boolToRat b) :
    let result := pushConst builder value
    Invariant result.1 (b :: stack) (result.2 :: vars) := by
  classical
  obtain ⟨hMatches, hBounded, hLen⟩ := hInv
  dsimp [pushConst]
  cases hFresh : Builder.fresh builder value with
  | mk builder₁ v =>
      have hvFresh_eq : (Builder.fresh builder value).2 = v :=
        congrArg Prod.snd hFresh
      have hv_idx : v = builder.nextVar := by
        have hvBase : (Builder.fresh builder value).2 = builder.nextVar :=
          Builder.fresh_snd (st := builder) (value := value)
        exact hvFresh_eq.symm.trans hvBase
      have hBuilder_eq : (Builder.fresh builder value).1 = builder₁ :=
        congrArg Prod.fst hFresh
      have hNext₁ : builder₁.nextVar = builder.nextVar + 1 := by
        have hNext :=
          Builder.fresh_nextVar (st := builder) (value := value)
        exact hBuilder_eq ▸ hNext
      have hMatches₁ : Matches builder₁ stack vars := by
        have hFreshMatches :=
          matches_fresh_preserve
            (builder := builder) (value := value)
            (stack := stack) (vars := vars) hMatches hBounded
        exact hBuilder_eq ▸ hFreshMatches
      have hBounded₁ : Bounded builder₁ vars := by
        have hFreshBounded :=
          Builder.fresh_preserve_bounded
            (st := builder) (value := value) (vars := vars) hBounded
        exact hBuilder_eq ▸ hFreshBounded
      have hAssign₁ : builder₁.assign v = value := by
        have hAssign :=
          Builder.fresh_assign_self (st := builder) (value := value)
        have hAssign' := hBuilder_eq ▸ hAssign
        exact hvFresh_eq ▸ hAssign'
      let builder₂ := Builder.addConstraint builder₁ (eqConstConstraint v value)
      have hMatches₂ : Matches builder₂ stack vars := by
        change
          Matches
            (Builder.addConstraint builder₁ (eqConstConstraint v value))
            stack vars
        exact addConstraint_preserve_matches hMatches₁ _
      have hBounded₂ : Bounded builder₂ vars := by
        change
          Bounded
            (Builder.addConstraint builder₁ (eqConstConstraint v value))
            vars
        exact addConstraint_preserve_bounded hBounded₁ _
      have hAssign₂ : builder₂.assign v = value := by
        have assign_eq :=
          Builder.addConstraint_assign (st := builder₁)
            (c := eqConstConstraint v value)
        exact assign_eq.symm ▸ hAssign₁
      let builder₃ := recordBoolean builder₂ v
      have hMatches₃ : Matches builder₃ stack vars := by
        change Matches (recordBoolean builder₂ v) stack vars
        exact
          recordBoolean_preserve_matches
            (builder := builder₂)
            (stack := stack) (vars := vars) (v := v) hMatches₂
      have hBounded₃ : Bounded builder₃ vars := by
        change Bounded (recordBoolean builder₂ v) vars
        exact
          recordBoolean_preserve_bounded
            (builder := builder₂) (vars := vars) (v := v) hBounded₂
      have hAssign₂_bool : builder₂.assign v = boolToRat b := by
        exact hvalue ▸ hAssign₂
      have hAssign₃ : builder₃.assign v = boolToRat b := by
        have : builder₃.assign v = builder₂.assign v := by
          simp [builder₃, builder₂, recordBoolean]
        exact this.trans hAssign₂_bool
      have hHead : boolToRat b = builder₃.assign v :=
        hAssign₃.symm
      have hNext₂ :
          builder₂.nextVar = builder₁.nextVar :=
        Builder.addConstraint_nextVar _ _
      have hNext₃ :
          builder₃.nextVar = builder₁.nextVar := by
        simp [builder₃, builder₂, Builder.recordBoolean_nextVar,
          Builder.addConstraint_nextVar]
      have hMatches_new :
          Matches builder₃ (b :: stack) (v :: vars) :=
        List.Forall₂.cons hHead hMatches₃
      have hBounded_new :
          Bounded builder₃ (v :: vars) := by
        intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · subst hw
          have hv_lt_builder₂ :
              builder.nextVar < builder₁.nextVar :=
            hNext₁ ▸ Nat.lt_succ_self _
          have hv_lt_builder₃ :
              builder.nextVar < builder₃.nextVar :=
            hNext₃ ▸ hv_lt_builder₂
          exact hv_idx.symm ▸ hv_lt_builder₃
        · exact hBounded₃ w hw
      have hMatches_new' :
          Matches builder₃ (b :: stack) (builder.nextVar :: vars) :=
        hv_idx ▸ hMatches_new
      have hBounded_new' :
          Bounded builder₃ (builder.nextVar :: vars) :=
        hv_idx ▸ hBounded_new
      have hLen_new :
          (b :: stack).length = (builder.nextVar :: vars).length := by
        simp [List.length_cons, hLen]
      have hGoal :
          Invariant builder₃ (b :: stack) (builder.nextVar :: vars) :=
        And.intro hMatches_new' (And.intro hBounded_new' hLen_new)
      exact hGoal

lemma pushConst_strong {builder : Builder} {stack : Stack}
    {vars : List Var} {value : ℚ} {b : Bool}
    (hStrong : StrongInvariant builder stack vars)
    (hvalue : value = boolToRat b) :
    let result := pushConst builder value
    StrongInvariant result.1 (b :: stack) (result.2 :: vars) := by
  classical
  obtain ⟨hMatches, hBounded, hSupport, hSat⟩ := hStrong
  dsimp [pushConst]
  cases hFresh : Builder.fresh builder value with
  | mk builder₁ v =>
      have hvFresh_eq : (Builder.fresh builder value).2 = v :=
        congrArg Prod.snd hFresh
      have hv_idx : v = builder.nextVar := by
        have hvBase : (Builder.fresh builder value).2 = builder.nextVar :=
          Builder.fresh_snd (st := builder) (value := value)
        exact hvFresh_eq.symm.trans hvBase
      have hBuilder_eq : (Builder.fresh builder value).1 = builder₁ :=
        congrArg Prod.fst hFresh
      have hNext₁ : builder₁.nextVar = builder.nextVar + 1 := by
        have hNext :=
          Builder.fresh_nextVar (st := builder) (value := value)
        exact hBuilder_eq ▸ hNext
      have hv_lt_next : v < builder₁.nextVar := by
        have hlt : builder.nextVar < builder₁.nextVar := by
          exact hNext₁.symm ▸ Nat.lt_succ_self _
        exact hv_idx ▸ hlt
      have hMatches₁ : Matches builder₁ stack vars := by
        have hFreshMatches :=
          matches_fresh_preserve
          (builder := builder) (value := value)
          (stack := stack) (vars := vars) hMatches hBounded
        exact hBuilder_eq ▸ hFreshMatches
      have hBounded₁ : Bounded builder₁ vars := by
        have hFreshBounded :=
          Builder.fresh_preserve_bounded
          (st := builder) (value := value) (vars := vars) hBounded
        exact hBuilder_eq ▸ hFreshBounded
      have hSupport₁ :
          SupportOK builder₁ := by
        have hFreshSupport :=
          Builder.fresh_preserve_support
            (st := builder) (value := value) hSupport
        exact hBuilder_eq ▸ hFreshSupport
      have hSat₁ :
          System.satisfied builder₁.assign (Builder.system builder₁) := by
        intro c hc
        have hc' :
            c ∈ (Builder.system (Builder.fresh builder value).1).constraints :=
          hBuilder_eq.symm ▸ hc
        have hSatFresh :
            System.satisfied (Builder.fresh builder value).1.assign
              (Builder.system (Builder.fresh builder value).1) :=
          Builder.fresh_preserve_satisfied_mem
            (st := builder) (value := value) hSupport hSat
        have hSat' := hSatFresh (c := c) hc'
        exact hBuilder_eq ▸ hSat'
      have hAssign₁ : builder₁.assign v = value := by
        have hAssign :=
          Builder.fresh_assign_self
          (st := builder) (value := value)
        have hAssign' := hBuilder_eq ▸ hAssign
        exact hvFresh_eq ▸ hAssign'
      let builder₂ := Builder.addConstraint builder₁ (eqConstConstraint v value)
      have hMatches₂ : Matches builder₂ stack vars := by
        change
          Matches
            (Builder.addConstraint builder₁ (eqConstConstraint v value))
            stack vars
        exact addConstraint_preserve_matches hMatches₁ _
      have hBounded₂ : Bounded builder₂ vars := by
        change
          Bounded
            (Builder.addConstraint builder₁ (eqConstConstraint v value))
            vars
        exact addConstraint_preserve_bounded hBounded₁ _
      have hSupport₂ :
          SupportOK builder₂ := by
        have hSubset :
            Constraint.support (eqConstConstraint v value) ⊆
              Finset.range builder₁.nextVar := by
          intro w hw
          have hw' := hw
          simp [eqConstConstraint_support] at hw'
          subst hw'
          exact Finset.mem_range.mpr hv_lt_next
        have hSupport' :=
          Builder.addConstraint_preserve_support
          (st := builder₁)
          (c := eqConstConstraint v value)
          hSupport₁ hSubset
        change
          SupportOK
            (Builder.addConstraint builder₁ (eqConstConstraint v value))
        exact hSupport'
      have hSat₂ :
          System.satisfied builder₂.assign (Builder.system builder₂) := by
        have hEqConstraint :
            Constraint.satisfied builder₁.assign (eqConstConstraint v value) :=
          eqConstConstraint_head_satisfied
            (assign := builder₁.assign) (v := v) (value := value) hAssign₁
        intro c hc
        have hSatAdd :
            System.satisfied
              (Builder.addConstraint builder₁ (eqConstConstraint v value)).assign
              (Builder.system (Builder.addConstraint builder₁ (eqConstConstraint v value))) :=
          Builder.addConstraint_preserve_satisfied_mem
            (st := builder₁)
            (c := eqConstConstraint v value)
            hSat₁ hEqConstraint
        change
          Constraint.satisfied
            (Builder.addConstraint builder₁ (eqConstConstraint v value)).assign
            c
        have hc' :
            c ∈ (Builder.system
              (Builder.addConstraint builder₁ (eqConstConstraint v value))).constraints :=
          hc
        exact hSatAdd (c := c) hc'
      let builder₃ := recordBoolean builder₂ v
      have hMatches₃ : Matches builder₃ stack vars := by
        change
          Matches (recordBoolean builder₂ v) stack vars
        exact
          recordBoolean_preserve_matches
            (builder := builder₂)
            (stack := stack) (vars := vars) (v := v) hMatches₂
      have hBounded₃ : Bounded builder₃ vars := by
        change
          Bounded (recordBoolean builder₂ v) vars
        exact
          recordBoolean_preserve_bounded
            (builder := builder₂) (v := v) hBounded₂
      have hNext₂ : builder₂.nextVar = builder₁.nextVar := by
        change
          (Builder.addConstraint builder₁ (eqConstConstraint v value)).nextVar =
            builder₁.nextVar
        exact Builder.addConstraint_nextVar _ _
      have hv_lt_next₂ : v < builder₂.nextVar := by
        exact hNext₂.symm ▸ hv_lt_next
      have hSupport₃ :
          SupportOK builder₃ :=
        recordBoolean_preserve_support
          (builder := builder₂) (v := v) hSupport₂ hv_lt_next₂
      have hAssign₂ : builder₂.assign v = value := by
        have assign_eq :
            builder₂.assign = builder₁.assign := by
          change
            (Builder.addConstraint builder₁ (eqConstConstraint v value)).assign =
              builder₁.assign
          exact Builder.addConstraint_assign _ _
        exact assign_eq.symm ▸ hAssign₁
      have hAssign₂_bool : builder₂.assign v = boolToRat b := by
        exact hvalue ▸ hAssign₂
      have hBoolEq :
          builder₂.assign v * (builder₂.assign v - 1) = 0 := by
        exact hAssign₂_bool.symm ▸ boolToRat_mul_self_sub_one b
      have hBoolConstraint :
          Constraint.satisfied builder₂.assign (boolConstraint v) :=
        (boolConstraint_satisfied (assign := builder₂.assign) (v := v)).2
          hBoolEq
      have hSat₃ :
          System.satisfied builder₃.assign (Builder.system builder₃) :=
        recordBoolean_preserve_satisfied_mem
          (builder := builder₂) (v := v) hSat₂ hBoolConstraint
      have hAssign₃ : builder₃.assign v = boolToRat b := by
        have : builder₃.assign v = builder₂.assign v := by
          simp [builder₃, builder₂, recordBoolean]
        exact this.trans hAssign₂_bool
      have hNext₃ : builder₃.nextVar = builder₁.nextVar := by
        simp [builder₃, builder₂, Builder.recordBoolean_nextVar,
          Builder.addConstraint_nextVar]
      have hHead :
          boolToRat b = builder₃.assign builder.nextVar := by
        exact (hv_idx ▸ hAssign₃).symm
      have hMatches_final :
          Matches builder₃ (b :: stack) (builder.nextVar :: vars) :=
        List.Forall₂.cons hHead hMatches₃
      have hBounded_final :
          Bounded builder₃ (builder.nextVar :: vars) := by
        intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · subst hw
          have hv_lt_builder₃ : v < builder₃.nextVar := by
            exact hNext₃.symm ▸ hv_lt_next
          exact hv_idx ▸ hv_lt_builder₃
        · exact hBounded₃ w hw
      have hSupport_new :
          SupportOK builder₃ := hSupport₃
      have hSat_new :
          System.satisfied builder₃.assign (Builder.system builder₃) :=
        hSat₃
      have hResult :
          pushConst builder value = (builder₃, v) := by
        simp [pushConst, hFresh, builder₂, builder₃]
      have hStrong_new :
          StrongInvariant builder₃ (b :: stack) (builder.nextVar :: vars) :=
        ⟨hMatches_final,
          ⟨hBounded_final, ⟨hSupport_new, hSat_new⟩⟩⟩
      have :
          StrongInvariant
            (recordBoolean
              (Builder.addConstraint builder₁ (eqConstConstraint builder.nextVar value))
              builder.nextVar)
            (b :: stack) (builder.nextVar :: vars) := by
        have hBuilder_eq :
            recordBoolean
                (Builder.addConstraint
                  builder₁
                  (eqConstConstraint builder.nextVar value))
                builder.nextVar =
              builder₃ := by
          subst hv_idx
          rfl
        exact hBuilder_eq ▸ hStrong_new
      exact this

lemma applyAnd_invariant {builder : Builder} {x y : Bool}
    {before : Stack} {vx vy : Var} {vars : List Var}
    (hInv : Invariant builder (x :: y :: before) (vx :: vy :: vars)) :
    Invariant
      (recordBoolean
        (Builder.addConstraint (Builder.fresh builder (boolToRat (y && x))).1
          { A := LinComb.single vx 1
            B := LinComb.single vy 1
            C := LinComb.single (Builder.fresh builder (boolToRat (y && x))).2 1 })
        (Builder.fresh builder (boolToRat (y && x))).2)
      ((y && x) :: before)
      ((Builder.fresh builder (boolToRat (y && x))).2 :: vars) := by
  classical
  let z : Bool := y && x
  let fres := Builder.fresh builder (boolToRat z)
  let builder1 := fres.1
  let vz := fres.2
  let builder2 := Builder.addConstraint builder1
    { A := LinComb.single vx 1
      B := LinComb.single vy 1
      C := LinComb.single vz 1 }
  let builder3 := recordBoolean builder2 vz
  change Invariant builder3 (z :: before) (vz :: vars)
  obtain ⟨hMatches, hBounded, hLen⟩ := hInv
  have hMatchesTail := matches_cons_tail hMatches
  have hMatchesRest : Matches builder before vars :=
    matches_cons_tail hMatchesTail
  have hBoundedTail : Bounded builder (vy :: vars) :=
    Bounded.tail hBounded
  have hBoundedRest : Bounded builder vars :=
    Bounded.tail hBoundedTail
  have hLenRest : before.length = vars.length :=
    matches_length_eq hMatchesRest
  have hFresh_builder :
      (Builder.fresh builder (boolToRat z)).1 = builder1 := rfl
  have hFresh_v :
      (Builder.fresh builder (boolToRat z)).2 = vz := rfl
  have hv_idx : vz = builder.nextVar := by
    simp [vz, fres]
  have hNext₁ : builder1.nextVar = builder.nextVar + 1 := by
    simp [builder1, fres]
  have hMatches1 : Matches builder1 (x :: y :: before) (vx :: vy :: vars) := by
    have hFreshMatches :=
      matches_fresh_preserve (builder := builder) (value := boolToRat z)
        (stack := x :: y :: before) (vars := vx :: vy :: vars) hMatches hBounded
    exact hFresh_builder ▸ hFreshMatches
  have hBounded1 : Bounded builder1 (vx :: vy :: vars) := by
    have hFreshBounded :=
      Builder.fresh_preserve_bounded (st := builder)
        (value := boolToRat z) (vars := vx :: vy :: vars) hBounded
    exact hFresh_builder ▸ hFreshBounded
  have hAssign1 : builder1.assign vz = boolToRat z := by
    have hFreshAssign :=
      Builder.fresh_assign_self (st := builder) (value := boolToRat z)
    have hAssignBuilder :
        builder1.assign ((Builder.fresh builder (boolToRat z)).2) = boolToRat z :=
      hFresh_builder ▸ hFreshAssign
    exact hFresh_v ▸ hAssignBuilder
  set builder2 := Builder.addConstraint builder1
    { A := LinComb.single vx 1
      B := LinComb.single vy 1
      C := LinComb.single vz 1 }
  have hMatches2 : Matches builder2 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches
        (Builder.addConstraint builder1
          { A := LinComb.single vx 1
            B := LinComb.single vy 1
            C := LinComb.single vz 1 })
        (x :: y :: before) (vx :: vy :: vars)
    exact addConstraint_preserve_matches hMatches1 _
  have hBounded2 : Bounded builder2 (vx :: vy :: vars) := by
    change
      Bounded
        (Builder.addConstraint builder1
          { A := LinComb.single vx 1
            B := LinComb.single vy 1
            C := LinComb.single vz 1 })
        (vx :: vy :: vars)
    exact addConstraint_preserve_bounded hBounded1 _
  set builder3 := recordBoolean builder2 vz
  have hMatches3 : Matches builder3 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches (recordBoolean builder2 vz) (x :: y :: before) (vx :: vy :: vars)
    exact
      recordBoolean_preserve_matches (builder := builder2)
        (stack := x :: y :: before) (vars := vx :: vy :: vars) (v := vz) hMatches2
  have hBounded3 : Bounded builder3 (vx :: vy :: vars) := by
    change Bounded (recordBoolean builder2 vz) (vx :: vy :: vars)
    exact
      recordBoolean_preserve_bounded (builder := builder2)
        (vars := vx :: vy :: vars) (v := vz) hBounded2
  have hMatchesRest3 : Matches builder3 before vars :=
    matches_tail_tail hMatches3
  have hBoundedRest3 : Bounded builder3 vars :=
    Bounded.tail_tail hBounded3
  have hAssign3 : builder3.assign vz = boolToRat z := by
    subst builder3
    simp [builder2, recordBoolean, hAssign1]
  have hHead : boolToRat z = builder3.assign vz :=
    hAssign3.symm
  have hMatches_new : Matches builder3 (z :: before) (vz :: vars) :=
    List.Forall₂.cons hHead hMatchesRest3
  have hNext₂ : builder2.nextVar = builder1.nextVar := by
    simp [builder2]
  have hNext₃ : builder3.nextVar = builder1.nextVar := by
    simp [builder3, builder2, Builder.recordBoolean_nextVar, Builder.addConstraint_nextVar]
  have hBounded_new : Bounded builder3 (vz :: vars) := by
    intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst hw
      have hv_lt_builder1 :
          builder.nextVar < builder1.nextVar :=
        hNext₁ ▸ Nat.lt_succ_self _
      have hv_lt_builder3 :
          builder.nextVar < builder3.nextVar :=
        hNext₃ ▸ hv_lt_builder1
      exact hv_idx.symm ▸ hv_lt_builder3
    · exact hBoundedRest3 w hw
  have hLen_new : (z :: before).length = (vz :: vars).length := by
    simp [List.length_cons, hLenRest]
  exact And.intro hMatches_new (And.intro hBounded_new hLen_new)

lemma applyAnd_strong {builder : Builder} {x y : Bool}
    {before : Stack} {vx vy : Var} {vars : List Var}
    (hStrong : StrongInvariant builder (x :: y :: before) (vx :: vy :: vars))
    (hvxB : builder.assign vx = 0 ∨ builder.assign vx = 1)
    (hvyB : builder.assign vy = 0 ∨ builder.assign vy = 1) :
    let z : Bool := y && x
    let fres := Builder.fresh builder (boolToRat z)
    let builder1 := fres.1
    let vz := fres.2
    let mulConstraint :
        Constraint :=
      { A := LinComb.single vx 1
        B := LinComb.single vy 1
        C := LinComb.single vz 1 }
    let builder2 := Builder.addConstraint builder1 mulConstraint
    let builder3 := recordBoolean builder2 vz
    StrongInvariant builder3 (z :: before) (vz :: vars) := by
  classical
  obtain ⟨hMatches, hBounded, hSupport, hSat⟩ := hStrong
  let z : Bool := y && x
  let fres := Builder.fresh builder (boolToRat z)
  let builder1 := fres.1
  let vz := fres.2
  let mulConstraint :
      Constraint :=
    { A := LinComb.single vx 1
      B := LinComb.single vy 1
      C := LinComb.single vz 1 }
  let builder2 := Builder.addConstraint builder1 mulConstraint
  let builder3 := recordBoolean builder2 vz

  have hvx_lt_base : vx < builder.nextVar :=
    hBounded vx (by simp)
  have hvy_lt_base : vy < builder.nextVar :=
    hBounded vy (by simp)
  have hvz_idx : vz = builder.nextVar := by
    simp [vz, fres]
  have hNext₁ : builder1.nextVar = builder.nextVar + 1 := by
    simp [builder1, fres]
  have hvx_lt : vx < builder1.nextVar := by
    have hx := Nat.lt_succ_of_lt hvx_lt_base
    exact hNext₁ ▸ hx
  have hvy_lt : vy < builder1.nextVar := by
    have hy := Nat.lt_succ_of_lt hvy_lt_base
    exact hNext₁ ▸ hy
  have hvz_lt : vz < builder1.nextVar := by
    have := Nat.lt_succ_self builder.nextVar
    have hz := this
    have hz' : builder.nextVar < builder1.nextVar := hNext₁ ▸ hz
    exact hvz_idx ▸ hz'
  have hFresh_builder :
      (Builder.fresh builder (boolToRat z)).1 = builder1 := by
    simp [builder1, fres]
  have hFresh_v :
      (Builder.fresh builder (boolToRat z)).2 = vz := by
    simp [vz, fres]

  have hOK1 : SupportOK builder1 := by
    have hSupportFresh :=
      Builder.fresh_preserve_support
        (st := builder) (value := boolToRat z) hSupport
    exact hFresh_builder ▸ hSupportFresh
  have hSat1 :
      System.satisfied builder1.assign (Builder.system builder1) := by
    intro c hc
    have hcFresh :
        c ∈ (Builder.system (Builder.fresh builder (boolToRat z)).1).constraints := by
      -- rewrite `builder1` back to the fresh form
      simpa [hFresh_builder] using hc
    have hSatFresh :
        System.satisfied (Builder.fresh builder (boolToRat z)).1.assign
          (Builder.system (Builder.fresh builder (boolToRat z)).1) :=
      Builder.fresh_preserve_satisfied_mem
        (st := builder) (value := boolToRat z) hSupport hSat
    have hSatFresh_c := hSatFresh (c := c) hcFresh
    have hAssign_eq :
        builder1.assign =
          (Builder.fresh builder (boolToRat z)).1.assign := by
      -- transport via cached equality for the fresh builder
      simp [hFresh_builder]
    have hSatFresh_c' :
        Constraint.satisfied builder1.assign c :=
      hAssign_eq ▸ hSatFresh_c
    exact hSatFresh_c'

  have hxFreshEq :
      builder1.assign vx = builder.assign vx := by
    have hFreshAssign :=
      Builder.fresh_assign_lt
        (st := builder) (value := boolToRat z) (w := vx) (hw := hvx_lt_base)
    exact hFresh_builder ▸ hFreshAssign
  have hyFreshEq :
      builder1.assign vy = builder.assign vy := by
    have hFreshAssign :=
      Builder.fresh_assign_lt
        (st := builder) (value := boolToRat z) (w := vy) (hw := hvy_lt_base)
    exact hFresh_builder ▸ hFreshAssign

  have hvx_assign :
      builder1.assign vx = boolToRat x := by
    have hx := matches_cons_head (builder := builder)
      (stack := y :: before) (vars := vy :: vars) hMatches
    -- hx : boolToRat x = builder.assign vx
    have hx' : builder.assign vx = boolToRat x := hx.symm
    exact hxFreshEq ▸ hx'
  have hMatches_tail :
      Matches builder (y :: before) (vy :: vars) :=
    matches_cons_tail hMatches
  have hvy_assign :
      builder1.assign vy = boolToRat y := by
    have hy := matches_cons_head
      (builder := builder) (stack := before) (vars := vars) hMatches_tail
    have hy' : builder.assign vy = boolToRat y := hy.symm
    exact hyFreshEq ▸ hy'
  have hvz_assign :
      builder1.assign vz = boolToRat z := by
    have hFreshAssign :=
      Builder.fresh_assign_self (st := builder) (value := boolToRat z)
    have hAssignBuilder :
        builder1.assign ((Builder.fresh builder (boolToRat z)).2) = boolToRat z :=
      hFresh_builder ▸ hFreshAssign
    exact hFresh_v ▸ hAssignBuilder

  have hMulSupport :
      Constraint.support mulConstraint ⊆ Finset.range builder1.nextVar :=
    mulConstraint_support_subset hvx_lt hvy_lt hvz_lt
  have hOK2 : SupportOK builder2 := by
    have hSupport2 :=
      Builder.addConstraint_preserve_support
      (st := builder1) (c := mulConstraint) hOK1 hMulSupport
    have builder2_eq :
        builder2 = Builder.addConstraint builder1 mulConstraint := rfl
    exact builder2_eq.symm ▸ hSupport2

  have hEq :
      builder1.assign vx * builder1.assign vy =
        builder1.assign vz := by
    calc
      builder1.assign vx * builder1.assign vy
          = boolToRat x * boolToRat y := by
            simp [hvx_assign, hvy_assign]
      _ = boolToRat (x && y) := (ZK.boolToRat_and x y).symm
      _ = boolToRat (y && x) := by
            cases x <;> cases y <;> simp
      _ = boolToRat z := rfl
      _ = builder1.assign vz := hvz_assign.symm

  have hHeadMul :
      Constraint.satisfied builder1.assign mulConstraint :=
    mul_head_satisfied_of_eq (a := builder1.assign) vx vy vz hEq

  have hSat2 :
      System.satisfied builder2.assign (Builder.system builder2) := by
    intro c hc
    -- analyze membership in the extended constraints list
    have hMemCons : c ∈ mulConstraint :: builder1.constraints := by
      -- system builders relate to the plain constraints via simp lemmas
      simpa [builder2, Builder.system_addConstraint, Builder.system_constraints]
        using hc
    have hCases : c = mulConstraint ∨ c ∈ builder1.constraints :=
      List.mem_cons.mp hMemCons
    cases hCases with
    | inl hEqC =>
        subst hEqC
        -- new constraint case
        -- new constraint is satisfied by `hHeadMul`; transport assignment
        have hSatNew' :
            Constraint.satisfied builder1.assign mulConstraint :=
          hHeadMul
        -- rewrite assignment equality
        simpa [builder2, Builder.addConstraint_assign]
          using hSatNew'
    | inr hOldMem =>
        -- pre-existing constraint case
        have hSatOld : Constraint.satisfied builder1.assign c :=
          hSat1 hOldMem
        have hSatOld' :
            Constraint.satisfied
              ((Builder.addConstraint builder1 mulConstraint).assign) c := by
          simpa [Builder.addConstraint_assign] using hSatOld
        simpa [builder2]
          using hSatOld'

  have hvxB1 :
      builder1.assign vx = 0 ∨ builder1.assign vx = 1 := by
    cases hvxB with
    | inl h0 =>
        exact Or.inl (hxFreshEq ▸ h0)
    | inr h1 =>
        exact Or.inr (hxFreshEq ▸ h1)
  have hvyB1 :
      builder1.assign vy = 0 ∨ builder1.assign vy = 1 := by
    cases hvyB with
    | inl h0 =>
        exact Or.inl (hyFreshEq ▸ h0)
    | inr h1 =>
        exact Or.inr (hyFreshEq ▸ h1)

  have hvzBoolProd :
      builder1.assign vx * builder1.assign vy = 0 ∨
        builder1.assign vx * builder1.assign vy = 1 :=
    boolean_mul_closed hvxB1 hvyB1
  have hvzBool1 :
      builder1.assign vz = 0 ∨ builder1.assign vz = 1 := by
    cases hvzBoolProd with
    | inl h0 =>
        exact Or.inl (hEq ▸ h0)
    | inr h1 =>
        exact Or.inr (hEq ▸ h1)
  have hvzBool2 :
      builder2.assign vz = 0 ∨ builder2.assign vz = 1 := by
    cases hvzBool1 with
    | inl h0 =>
        have assign_eq :=
          congrArg (fun f => f vz)
            (Builder.addConstraint_assign (st := builder1) (c := mulConstraint)).symm
        have assign_eq' : builder1.assign vz = builder2.assign vz := by
          change builder1.assign vz =
            (Builder.addConstraint builder1 mulConstraint).assign vz
          exact assign_eq
        exact Or.inl (assign_eq' ▸ h0)
    | inr h1 =>
        have assign_eq :=
          congrArg (fun f => f vz)
            (Builder.addConstraint_assign (st := builder1) (c := mulConstraint)).symm
        have assign_eq' : builder1.assign vz = builder2.assign vz := by
          change builder1.assign vz =
            (Builder.addConstraint builder1 mulConstraint).assign vz
          exact assign_eq
        exact Or.inr (assign_eq' ▸ h1)

  have hvzBoolEq :
      builder2.assign vz * (builder2.assign vz - 1) = 0 := by
    cases hvzBool2 with
    | inl h0 => simp [h0]
    | inr h1 => simp [h1]

  have hvzConstraint :
      Constraint.satisfied builder2.assign (boolConstraint vz) :=
    (boolConstraint_satisfied (assign := builder2.assign) (v := vz)).2 hvzBoolEq

  have hvz_lt_next2 : vz < builder2.nextVar := by
    have next_eq :=
      (Builder.addConstraint_nextVar (st := builder1) (c := mulConstraint)).symm
    have next_eq' : builder1.nextVar = builder2.nextVar := by
      change builder1.nextVar =
        (Builder.addConstraint builder1 mulConstraint).nextVar
      exact next_eq
    exact next_eq' ▸ hvz_lt

  have hOK3 : SupportOK builder3 :=
    recordBoolean_preserve_support
      (builder := builder2) (v := vz) hOK2 hvz_lt_next2
  have hSat3 :
      System.satisfied builder3.assign (Builder.system builder3) := by
    intro c hc
    have hc' :
        c = boolConstraint vz ∨ c ∈ builder2.constraints := by
      have hc'' := hc
      simp [builder3, Builder.system_recordBoolean] at hc''
      exact hc''
    have hAssign :
        builder3.assign = builder2.assign := by
      simp [builder3]
    cases hc' with
    | inl hEq =>
        subst hEq
        exact hAssign ▸ hvzConstraint
    | inr hMem =>
        have hSat := hSat2 hMem
        exact hAssign ▸ hSat

  have hInvariantInput :
      Invariant builder (x :: y :: before) (vx :: vy :: vars) :=
    ⟨hMatches, hBounded, matches_length_eq hMatches⟩

  have hInvariant :
      Invariant builder3 (z :: before) (vz :: vars) := by
    change
      Invariant
        (recordBoolean
          (Builder.addConstraint (Builder.fresh builder (boolToRat (y && x))).1
            { A := LinComb.single vx 1
              B := LinComb.single vy 1
              C := LinComb.single (Builder.fresh builder (boolToRat (y && x))).2 1 })
          (Builder.fresh builder (boolToRat (y && x))).2)
        ((y && x) :: before)
        ((Builder.fresh builder (boolToRat (y && x))).2 :: vars)
    exact
      (applyAnd_invariant
        (builder := builder) (x := x) (y := y) (before := before)
        (vx := vx) (vy := vy) (vars := vars) (hInv := hInvariantInput))

  exact ⟨hInvariant.1, hInvariant.2.1, hOK3, hSat3⟩

lemma applyOr_strong {builder : Builder} {x y : Bool}
    {before : Stack} {vx vy : Var} {vars : List Var}
    (hStrong : StrongInvariant builder (x :: y :: before) (vx :: vy :: vars))
    (_hvxB : builder.assign vx = 0 ∨ builder.assign vx = 1)
    (_hvyB : builder.assign vy = 0 ∨ builder.assign vy = 1) :
    let z : Bool := y || x
    let mulVal := boolToRat (y && x)
    let fresMul := Builder.fresh builder mulVal
    let builder1 := fresMul.1
    let vmul := fresMul.2
    let builder2 :=
      Builder.addConstraint builder1
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 }
    let builder3 := recordBoolean builder2 vmul
    let fresZ := Builder.fresh builder3 (boolToRat z)
    let builder4 := fresZ.1
    let vz := fresZ.2
    let eqOr := eqConstraint (linhead_or vz vx vy vmul) (LinComb.ofConst 0)
    let builder5 := Builder.addConstraint builder4 eqOr
    let builder6 := recordBoolean builder5 vz
    StrongInvariant builder6 (z :: before) (vz :: vars) := by
  classical
  obtain ⟨hMatches, hBounded, hSupport, hSat⟩ := hStrong
  let z : Bool := y || x
  let mulVal := boolToRat (y && x)
  let fresMul := Builder.fresh builder mulVal
  let builder1 := fresMul.1
  let vmul := fresMul.2
  let builder2 :=
    Builder.addConstraint builder1
      { A := LinComb.single vy 1
        B := LinComb.single vx 1
        C := LinComb.single vmul 1 }
  let builder3 := recordBoolean builder2 vmul
  let fresZ := Builder.fresh builder3 (boolToRat z)
  let builder4 := fresZ.1
  let vz := fresZ.2
  let eqOr := eqConstraint (linhead_or vz vx vy vmul) (LinComb.ofConst 0)
  let builder5 := Builder.addConstraint builder4 eqOr
  let builder6 := recordBoolean builder5 vz

  have hFreshMul_builder :
      (Builder.fresh builder mulVal).1 = builder1 := rfl
  have hFreshMul_v :
      (Builder.fresh builder mulVal).2 = vmul := rfl
  have hFreshZ_builder :
      (Builder.fresh builder3 (boolToRat z)).1 = builder4 := rfl
  have hFreshZ_v :
      (Builder.fresh builder3 (boolToRat z)).2 = vz := rfl

  have hvx_lt_base : vx < builder.nextVar :=
    hBounded vx (by simp)
  have hvy_lt_base : vy < builder.nextVar :=
    hBounded vy (by simp)
  have hvmul_idx : vmul = builder.nextVar := by
    simp [vmul, fresMul]
  have hbuilder1_next :
      builder1.nextVar = builder.nextVar + 1 := by
    simp [builder1, fresMul]

  have hx_head :=
    matches_cons_head
      (builder := builder) (b := x)
      (stack := y :: before) (v := vx) (vars := vy :: vars) hMatches
  have hvx_assign_base : builder.assign vx = boolToRat x := hx_head.symm
  have hy_tail :=
    matches_cons_tail
      (builder := builder) (b := x)
      (stack := y :: before) (v := vx) (vars := vy :: vars) hMatches
  have hy_head :=
    matches_cons_head
      (builder := builder) (b := y)
      (stack := before) (v := vy) (vars := vars) hy_tail
  have hvy_assign_base : builder.assign vy = boolToRat y := hy_head.symm

  have hMatches1 :
      Matches builder1 (x :: y :: before) (vx :: vy :: vars) := by
    have hFreshMatches :=
      matches_fresh_preserve
        (builder := builder)
        (stack := x :: y :: before)
        (vars := vx :: vy :: vars)
        (value := mulVal) hMatches hBounded
    exact hFreshMatches
  have hBounded1 :
      Bounded builder1 (vx :: vy :: vars) := by
    have hFreshBounded :=
      Builder.fresh_preserve_bounded
        (st := builder) (value := mulVal) (vars := vx :: vy :: vars) hBounded
    exact hFreshBounded
  have hSupport1 :
      SupportOK builder1 := by
    have hFreshSupport :=
      Builder.fresh_preserve_support
        (st := builder) (value := mulVal) hSupport
    exact hFreshSupport
  have hSat1 :
      System.satisfied builder1.assign (Builder.system builder1) :=
    Builder.fresh_preserve_satisfied_mem
      (st := builder) (value := mulVal) hSupport hSat

  have hvx_lt1 : vx < builder1.nextVar :=
    hbuilder1_next ▸ Nat.lt_succ_of_lt hvx_lt_base
  have hvy_lt1 : vy < builder1.nextVar :=
    hbuilder1_next ▸ Nat.lt_succ_of_lt hvy_lt_base
  have hvmul_lt1 : vmul < builder1.nextVar :=
    hvmul_idx ▸ (hbuilder1_next ▸ Nat.lt_succ_self builder.nextVar)

  have hvx_assign1 :
      builder1.assign vx = boolToRat x := by
    have hAssign :=
      Builder.fresh_assign_lt
        (st := builder) (value := mulVal) (w := vx) (hw := hvx_lt_base)
    have hxFresh := hFreshMul_builder ▸ hAssign
    exact hxFresh.trans hvx_assign_base
  have hvy_assign1 :
      builder1.assign vy = boolToRat y := by
    have hAssign :=
      Builder.fresh_assign_lt
        (st := builder) (value := mulVal) (w := vy) (hw := hvy_lt_base)
    have hyFresh := hFreshMul_builder ▸ hAssign
    exact hyFresh.trans hvy_assign_base
  have hvmul_assign1 :
      builder1.assign vmul = boolToRat (y && x) := by
    have hAssign :=
      Builder.fresh_assign_self (st := builder) (value := mulVal)
    have hAssign' := hFreshMul_builder ▸ hAssign
    have hAssign'' := hFreshMul_v ▸ hAssign'
    calc
      builder1.assign vmul
          = mulVal := hAssign''
      _ = boolToRat (y && x) := rfl

  have hMatches2_raw :
      Matches
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
        (x :: y :: before) (vx :: vy :: vars) :=
    addConstraint_preserve_matches hMatches1
      { A := LinComb.single vy 1
        B := LinComb.single vx 1
        C := LinComb.single vmul 1 }
  have hMatches2 :
      Matches builder2 (x :: y :: before) (vx :: vy :: vars) :=
    by
      change
        Matches
          (Builder.addConstraint builder1
            { A := LinComb.single vy 1
              B := LinComb.single vx 1
              C := LinComb.single vmul 1 })
          (x :: y :: before) (vx :: vy :: vars)
      exact hMatches2_raw
  have hBounded2_raw :
      Bounded
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
        (vx :: vy :: vars) :=
    addConstraint_preserve_bounded hBounded1
      { A := LinComb.single vy 1
        B := LinComb.single vx 1
        C := LinComb.single vmul 1 }
  have hBounded2 :
      Bounded builder2 (vx :: vy :: vars) :=
    by
      change
        Bounded
          (Builder.addConstraint builder1
            { A := LinComb.single vy 1
              B := LinComb.single vx 1
              C := LinComb.single vmul 1 })
          (vx :: vy :: vars)
      exact hBounded2_raw
  have hSupportMul :
      Constraint.support
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 } ⊆
          Finset.range builder1.nextVar :=
    mulConstraint_support_subset
      (n := builder1.nextVar)
      (vx := vy) (vy := vx) (vz := vmul)
      hvy_lt1 hvx_lt1 hvmul_lt1
  have hSupport2_raw :=
    Builder.addConstraint_preserve_support
      (st := builder1)
      (c :=
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 })
      hSupport1 hSupportMul
  have hSupport2 :
      SupportOK builder2 :=
    by
      change
        SupportOK
          (Builder.addConstraint builder1
            { A := LinComb.single vy 1
              B := LinComb.single vx 1
              C := LinComb.single vmul 1 })
      exact hSupport2_raw

  have hMulEq :
      builder1.assign vy * builder1.assign vx =
        builder1.assign vmul := by
    calc
      builder1.assign vy * builder1.assign vx
          = boolToRat y * boolToRat x := by
            simp [hvy_assign1, hvx_assign1]
      _ = boolToRat (y && x) := (ZK.boolToRat_and y x).symm
      _ = builder1.assign vmul := hvmul_assign1.symm

  have hMulSat :
      Constraint.satisfied builder1.assign
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 } :=
    mul_head_satisfied_of_eq
      (a := builder1.assign) (vx := vy) (vy := vx) (vz := vmul) hMulEq

  have hSat2 :
      System.satisfied builder2.assign (Builder.system builder2) :=
    Builder.addConstraint_preserve_satisfied_mem
      (st := builder1)
      (c :=
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 })
      hSat1 hMulSat

  have hvmul_assign2 :
      builder2.assign vmul = boolToRat (y && x) := by
    have hAssign_eq :=
      congrArg (fun f => f vmul)
        (Builder.addConstraint_assign (st := builder1)
          (c :=
            { A := LinComb.single vy 1
              B := LinComb.single vx 1
              C := LinComb.single vmul 1 }))
    exact hAssign_eq.trans hvmul_assign1
  have hvmul_bool :
      Constraint.satisfied builder2.assign (boolConstraint vmul) := by
    have hEq :
        builder2.assign vmul * (builder2.assign vmul - 1) = 0 := by
      -- use calc with explicit rewrite instead of simpa
      calc
        builder2.assign vmul * (builder2.assign vmul - 1)
            = boolToRat (y && x) * (boolToRat (y && x) - 1) := by
                  simp [hvmul_assign2]
        _ = 0 := ZK.boolToRat_sq_sub (y && x)
    exact
      (boolConstraint_satisfied (assign := builder2.assign) (v := vmul)).2 hEq

  have builder2_nextVar_eq : builder2.nextVar = builder1.nextVar := by
    simp [builder2]
  have hvmul_lt2 : vmul < builder2.nextVar :=
    builder2_nextVar_eq ▸ hvmul_lt1
  have hSupport3 :
      SupportOK builder3 :=
    recordBoolean_preserve_support
      (builder := builder2) (v := vmul) hSupport2 hvmul_lt2
  have hSat3 :
      System.satisfied builder3.assign (Builder.system builder3) :=
    recordBoolean_preserve_satisfied_mem
      (builder := builder2) (v := vmul) hSat2 hvmul_bool
  have hMatches3 :
      Matches builder3 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches (recordBoolean builder2 vmul) (x :: y :: before)
        (vx :: vy :: vars)
    exact recordBoolean_preserve_matches
      (builder := builder2) (v := vmul) hMatches2
  have hBounded3 :
      Bounded builder3 (vx :: vy :: vars) := by
    change Bounded (recordBoolean builder2 vmul) (vx :: vy :: vars)
    exact recordBoolean_preserve_bounded
      (builder := builder2) (v := vmul) hBounded2
  have hvz_idx : vz = builder3.nextVar := by
    simp [vz, fresZ]
  have hbuilder4_next :
      builder4.nextVar = builder3.nextVar + 1 := by
    simp [builder4, fresZ]

  have hMatches4 :
      Matches builder4 (x :: y :: before) (vx :: vy :: vars) := by
    have hFreshMatches :=
      matches_fresh_preserve
        (builder := builder3)
        (stack := x :: y :: before)
        (vars := vx :: vy :: vars)
        (value := boolToRat z) hMatches3 hBounded3
    exact hFreshZ_builder ▸ hFreshMatches
  have hBounded4 :
      Bounded builder4 (vx :: vy :: vars) := by
    have hFreshBounded :=
      Builder.fresh_preserve_bounded
        (st := builder3) (value := boolToRat z)
        (vars := vx :: vy :: vars) hBounded3
    exact hFreshZ_builder ▸ hFreshBounded
  have hSupport4 :
      SupportOK builder4 := by
    have hFreshSupport :=
      Builder.fresh_preserve_support
        (st := builder3) (value := boolToRat z) hSupport3
    exact hFreshZ_builder ▸ hFreshSupport
  have hSat4 :
      System.satisfied builder4.assign (Builder.system builder4) :=
    Builder.fresh_preserve_satisfied_mem
      (st := builder3) (value := boolToRat z) hSupport3 hSat3

  have hvx_lt3 : vx < builder3.nextVar :=
    hBounded3 vx (by simp)
  have hvy_lt3 : vy < builder3.nextVar :=
    hBounded3 vy (by simp)
  have hvmul_lt3 :
      vmul < builder3.nextVar := by
    have : vmul < builder1.nextVar := hvmul_lt1
    -- avoid simpa; use equality to transport the inequality
    have hEq : builder3.nextVar = builder1.nextVar := by
      simp [builder3, builder2, Builder.recordBoolean_nextVar,
        Builder.addConstraint_nextVar]
    exact hEq.symm ▸ this

  have hvx_assign4 :
      builder4.assign vx = boolToRat x := by
    have hFresh := Builder.fresh_assign_lt
      (st := builder3) (value := boolToRat z)
      (w := vx) (hw := hvx_lt3)
    have hFresh' : builder4.assign vx = builder3.assign vx := by
      -- rewrite via cached equality rather than simpa
      rw [hFreshZ_builder] at hFresh
      exact hFresh
    have hRec1 : builder3.assign vx = builder2.assign vx := by
      simp [builder3, Builder.recordBoolean_assign]
    have hRec2 : builder2.assign vx = builder1.assign vx := by
      simp [builder2, Builder.addConstraint_assign]
    exact (hFresh'.trans (hRec1.trans (hRec2.trans hvx_assign1)))
  have hvy_assign4 :
      builder4.assign vy = boolToRat y := by
    have hFresh := Builder.fresh_assign_lt
      (st := builder3) (value := boolToRat z)
      (w := vy) (hw := hvy_lt3)
    have hFresh' : builder4.assign vy = builder3.assign vy := by
      rw [hFreshZ_builder] at hFresh
      exact hFresh
    have hRec1 : builder3.assign vy = builder2.assign vy := by
      simp [builder3, Builder.recordBoolean_assign]
    have hRec2 : builder2.assign vy = builder1.assign vy := by
      simp [builder2, Builder.addConstraint_assign]
    exact (hFresh'.trans (hRec1.trans (hRec2.trans hvy_assign1)))
  have hvmul_assign4 :
      builder4.assign vmul = boolToRat (y && x) := by
    -- thread assignment equalities without enabling extra simp rewrites
    have hFresh :=
      Builder.fresh_assign_lt
        (st := builder3) (value := boolToRat z)
        (w := vmul) (hw := hvmul_lt3)
    have hFresh' : builder4.assign vmul = builder3.assign vmul := by
      rw [hFreshZ_builder] at hFresh
      exact hFresh
    have hRecBool : builder3.assign vmul = builder2.assign vmul := by
      simp [builder3, Builder.recordBoolean_assign]
    exact (hFresh'.trans hRecBool).trans hvmul_assign2
  have hvz_assign4 :
      builder4.assign vz = boolToRat z := by
    have := Builder.fresh_assign_self
      (st := builder3) (value := boolToRat z)
    -- rewrite via cached equality
    simpa [hFreshZ_builder] using this

  have hvz_lt4 :
      vz < builder4.nextVar := by
    have hlt : builder3.nextVar < builder4.nextVar := by
      simp [builder4, fresZ]
    simpa [hvz_idx] using hlt
  have hvx_lt4 :
      vx < builder4.nextVar := by
    have h0 : vx < builder3.nextVar + 1 := Nat.lt_succ_of_lt hvx_lt3
    -- rewrite target using cached equality
    simpa [hFreshZ_builder] using (by
      -- convert RHS with `hbuilder4_next`
      simpa [hbuilder4_next] using h0)
  have hvy_lt4 :
      vy < builder4.nextVar := by
    have h0 : vy < builder3.nextVar + 1 := Nat.lt_succ_of_lt hvy_lt3
    simpa [hbuilder4_next] using h0
  have hvmul_lt4 :
      vmul < builder4.nextVar := by
    have h0 : vmul < builder3.nextVar + 1 := Nat.lt_succ_of_lt hvmul_lt3
    simpa [hbuilder4_next] using h0

  have hLinSubset :
      (linhead_or vz vx vy vmul).support ⊆
        Finset.range builder4.nextVar := by
    exact subset_trans
      (linhead_or_support vz vx vy vmul)
      (four_var_support_subset
        (n := builder4.nextVar)
        hvz_lt4 hvx_lt4 hvy_lt4 hvmul_lt4)

  have hSupport5 :
      SupportOK builder5 := by
    have hConstraintSubset :
        Constraint.support eqOr ⊆ Finset.range builder4.nextVar := by
      intro w hw
      have hw' :
          w ∈ (linhead_or vz vx vy vmul).support := by
        simpa [eqOr, eqConstraint, Constraint.support,
          LinComb.support_ofConst, Finset.union_empty,
          Finset.empty_union, Finset.union_assoc] using hw
      exact hLinSubset hw'
    have h := Builder.addConstraint_preserve_support
      (st := builder4) (c := eqOr) hSupport4 hConstraintSubset
    exact h

  have hMulClosed :
      builder4.assign vmul = builder4.assign vx * builder4.assign vy := by
    calc
      builder4.assign vmul
          = boolToRat (y && x) := by simp [hvmul_assign4]
      _ = boolToRat (x && y) := by
            simp [Bool.and_comm]
      _ = boolToRat x * boolToRat y :=
            ZK.boolToRat_and x y
      _ = builder4.assign vx * builder4.assign vy := by
            simp [hvx_assign4, hvy_assign4]
  have hOrClosed :
      builder4.assign vz =
        builder4.assign vx + builder4.assign vy -
          builder4.assign vx * builder4.assign vy := by
    calc
      builder4.assign vz
          = boolToRat z := by simp [hvz_assign4]
      _ = boolToRat (y || x) := rfl
      _ = boolToRat (x || y) := by
            simp [Bool.or_comm]
      _ = boolToRat x + boolToRat y - boolToRat x * boolToRat y :=
            ZK.boolToRat_or x y
      _ = builder4.assign vx + builder4.assign vy -
          builder4.assign vx * builder4.assign vy := by
            simp [hvx_assign4, hvy_assign4]

  have hEqConstraint :
      Constraint.satisfied builder4.assign eqOr :=
    head_satisfied_or
      (a := builder4.assign) (vx := vx) (vy := vy)
      (vmul := vmul) (vz := vz) hMulClosed hOrClosed

  have hMatches5 :
      Matches builder5 (x :: y :: before) (vx :: vy :: vars) := by
    have h := addConstraint_preserve_matches hMatches4 eqOr
    exact h
  have hBounded5 :
      Bounded builder5 (vx :: vy :: vars) := by
    have h := addConstraint_preserve_bounded hBounded4 eqOr
    exact h
  have hSat5 :
      System.satisfied builder5.assign (Builder.system builder5) :=
    Builder.addConstraint_preserve_satisfied_mem
      (st := builder4) (c := eqOr) hSat4 hEqConstraint

  have hvz_assign5 :
      builder5.assign vz = boolToRat z := by
    -- transport via the cached addConstraint assignment equality
    have hAssign :=
      (Builder.addConstraint_assign (st := builder4) (c := eqOr)).symm
    -- apply both sides at `vz`
    exact (congrArg (fun f => f vz) hAssign) ▸ hvz_assign4
  have hBoolZ :
      Constraint.satisfied builder5.assign (boolConstraint vz) := by
    have hEq :
        builder5.assign vz * (builder5.assign vz - 1) = 0 := by
      calc
        builder5.assign vz * (builder5.assign vz - 1)
            = boolToRat z * (boolToRat z - 1) := by
                simp [hvz_assign5]
        _ = 0 := ZK.boolToRat_sq_sub z
    exact
      (boolConstraint_satisfied (assign := builder5.assign) (v := vz)).2 hEq

  have hSupport6 :
      SupportOK builder6 :=
    recordBoolean_preserve_support
      (builder := builder5) (v := vz) hSupport5
      (by
        -- transport the bound via nextVar equality
        have hlt : vz < builder4.nextVar := hvz_lt4
        have hEqNext : builder5.nextVar = builder4.nextVar := by
          simp [builder5, builder4, eqOr, Builder.addConstraint_nextVar, fresZ]
        exact hEqNext.symm ▸ hlt)
  have hSat6 :
      System.satisfied builder6.assign (Builder.system builder6) :=
    recordBoolean_preserve_satisfied_mem
      (builder := builder5) (v := vz) hSat5 hBoolZ
  have hMatches6 :
      Matches builder6 (x :: y :: before) (vx :: vy :: vars) := by
    have h :=
      recordBoolean_preserve_matches
        (builder := builder5) (v := vz) hMatches5
    exact h
  have hBounded6 :
      Bounded builder6 (vx :: vy :: vars) := by
    have h :=
      recordBoolean_preserve_bounded
        (builder := builder5) (v := vz) hBounded5
    exact h

  have hMatchesTail6 :
      Matches builder6 before vars :=
    matches_tail_tail hMatches6
  have hvz_assign6 :
      builder6.assign vz = boolToRat z := by
    -- rewrite using the cached recordBoolean assignment equality
    have hAssign := Builder.recordBoolean_assign (st := builder5) (v := vz)
    exact (congrArg (fun f => f vz) hAssign).trans hvz_assign5
  have hMatchesFinal :
      Matches builder6 (z :: before) (vz :: vars) :=
    List.Forall₂.cons hvz_assign6.symm hMatchesTail6

  have hBoundedTail6 :
      Bounded builder6 vars :=
    Bounded.tail_tail hBounded6
  have hnext_builder6 :
      builder6.nextVar = builder4.nextVar := by
    simp [builder6, builder5, builder4, eqOr,
      Builder.recordBoolean_nextVar, Builder.addConstraint_nextVar, fresZ]
  have hBoundedFinal :
      Bounded builder6 (vz :: vars) := by
    intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst hw
      have hlt := hvz_lt4
      -- rewrite the inequality target using nextVar equality
      have hEqNext : builder6.nextVar = builder4.nextVar := hnext_builder6
      simpa [hEqNext] using hlt
    · exact hBoundedTail6 w hw

  exact ⟨hMatchesFinal, ⟨hBoundedFinal, ⟨hSupport6, hSat6⟩⟩⟩

lemma applyImp_strong {builder : Builder} {x y : Bool}
    {before : Stack} {vx vy : Var} {vars : List Var}
    (hStrong : StrongInvariant builder (x :: y :: before) (vx :: vy :: vars))
    (_hvxB : builder.assign vx = 0 ∨ builder.assign vx = 1)
    (_hvyB : builder.assign vy = 0 ∨ builder.assign vy = 1) :
    let z : Bool := (! y) || x
    let mulVal := boolToRat (y && x)
    let fresMul := Builder.fresh builder mulVal
    let builder1 := fresMul.1
    let vmul := fresMul.2
    let builder2 :=
      Builder.addConstraint builder1
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 }
    let builder3 := recordBoolean builder2 vmul
    let fresZ := Builder.fresh builder3 (boolToRat z)
    let builder4 := fresZ.1
    let vz := fresZ.2
    let eqImp := eqConstraint (linhead_imp vz vx vy vmul) (LinComb.ofConst 0)
    let builder5 := Builder.addConstraint builder4 eqImp
    let builder6 := recordBoolean builder5 vz
    StrongInvariant builder6 (z :: before) (vz :: vars) := by
  classical
  obtain ⟨hMatches, hBounded, hSupport, hSat⟩ := hStrong
  let z : Bool := (! y) || x
  let mulVal := boolToRat (y && x)
  let fresMul := Builder.fresh builder mulVal
  let builder1 := fresMul.1
  let vmul := fresMul.2
  let builder2 :=
    Builder.addConstraint builder1
      { A := LinComb.single vy 1
        B := LinComb.single vx 1
        C := LinComb.single vmul 1 }
  let builder3 := recordBoolean builder2 vmul
  let fresZ := Builder.fresh builder3 (boolToRat z)
  let builder4 := fresZ.1
  let vz := fresZ.2
  let eqImp := eqConstraint (linhead_imp vz vx vy vmul) (LinComb.ofConst 0)
  let builder5 := Builder.addConstraint builder4 eqImp
  let builder6 := recordBoolean builder5 vz

  have hFreshMul_builder :
      (Builder.fresh builder mulVal).1 = builder1 := by
    change fresMul.1 = builder1
    rfl
  have hFreshMul_v :
      (Builder.fresh builder mulVal).2 = vmul := by
    change fresMul.2 = vmul
    rfl
  have hFreshZ_builder :
      (Builder.fresh builder3 (boolToRat z)).1 = builder4 := by
    change fresZ.1 = builder4
    rfl
  have hFreshZ_v :
      (Builder.fresh builder3 (boolToRat z)).2 = vz := by
    change fresZ.2 = vz
    rfl

  have hvx_lt_base : vx < builder.nextVar :=
    hBounded vx (by simp)
  have hvy_lt_base : vy < builder.nextVar :=
    hBounded vy (by simp)
  have hvmul_idx : vmul = builder.nextVar :=
    hFreshMul_v ▸ Builder.fresh_snd (st := builder) (value := mulVal)
  have hbuilder1_next :
      builder1.nextVar = builder.nextVar + 1 :=
    hFreshMul_builder ▸
      Builder.fresh_nextVar (st := builder) (value := mulVal)

  have hx_head :=
    matches_cons_head
      (builder := builder) (b := x)
      (stack := y :: before) (v := vx) (vars := vy :: vars) hMatches
  have hvx_assign_base : builder.assign vx = boolToRat x := hx_head.symm
  have hy_tail :=
    matches_cons_tail
      (builder := builder) (b := x)
      (stack := y :: before) (v := vx) (vars := vy :: vars) hMatches
  have hy_head :=
    matches_cons_head
      (builder := builder) (b := y)
      (stack := before) (v := vy) (vars := vars) hy_tail
  have hvy_assign_base : builder.assign vy = boolToRat y := hy_head.symm

  have hMatches1_raw :=
    matches_fresh_preserve
      (builder := builder)
      (stack := x :: y :: before)
      (vars := vx :: vy :: vars)
      (value := mulVal) hMatches hBounded
  have hMatches1 :
      Matches builder1 (x :: y :: before) (vx :: vy :: vars) :=
    hFreshMul_builder ▸ hMatches1_raw
  have hBounded1_raw :=
    Builder.fresh_preserve_bounded
      (st := builder) (value := mulVal) (vars := vx :: vy :: vars) hBounded
  have hBounded1 :
      Bounded builder1 (vx :: vy :: vars) :=
    hFreshMul_builder ▸ hBounded1_raw
  have hSupport1_raw :=
    Builder.fresh_preserve_support
      (st := builder) (value := mulVal) hSupport
  have hSupport1 :
      SupportOK builder1 :=
    hFreshMul_builder ▸ hSupport1_raw
  have hSat1 :
      System.satisfied builder1.assign (Builder.system builder1) :=
    Builder.fresh_preserve_satisfied_mem
      (st := builder) (value := mulVal) hSupport hSat

  have hvx_lt1 : vx < builder1.nextVar :=
    hbuilder1_next ▸ Nat.lt_succ_of_lt hvx_lt_base
  have hvy_lt1 : vy < builder1.nextVar :=
    hbuilder1_next ▸ Nat.lt_succ_of_lt hvy_lt_base
  have hvmul_lt1 : vmul < builder1.nextVar :=
    hvmul_idx ▸ (hbuilder1_next ▸ Nat.lt_succ_self builder.nextVar)

  have hvx_assign1 :
      builder1.assign vx = boolToRat x := by
    have hAssign :=
      Builder.fresh_assign_lt
        (st := builder) (value := mulVal) (w := vx) (hw := hvx_lt_base)
    exact (hFreshMul_builder ▸ hAssign).trans hvx_assign_base
  have hvy_assign1 :
      builder1.assign vy = boolToRat y := by
    have hAssign :=
      Builder.fresh_assign_lt
        (st := builder) (value := mulVal) (w := vy) (hw := hvy_lt_base)
    exact (hFreshMul_builder ▸ hAssign).trans hvy_assign_base
  have hvmul_assign1 :
      builder1.assign vmul = boolToRat (y && x) := by
    have hAssign :=
      Builder.fresh_assign_self (st := builder) (value := mulVal)
    have hAssign' := hFreshMul_builder ▸ hAssign
    have hAssign'' := hFreshMul_v ▸ hAssign'
    exact hAssign''.trans rfl

  have hMatches2_raw :
      Matches
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
        (x :: y :: before) (vx :: vy :: vars) :=
    addConstraint_preserve_matches hMatches1
      { A := LinComb.single vy 1
        B := LinComb.single vx 1
        C := LinComb.single vmul 1 }
  have hMatches2 :
      Matches builder2 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
        (x :: y :: before) (vx :: vy :: vars)
    exact hMatches2_raw
  have hBounded2_raw :
      Bounded
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
        (vx :: vy :: vars) :=
    addConstraint_preserve_bounded hBounded1
      { A := LinComb.single vy 1
        B := LinComb.single vx 1
        C := LinComb.single vmul 1 }
  have hBounded2 :
      Bounded builder2 (vx :: vy :: vars) := by
    change
      Bounded
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
        (vx :: vy :: vars)
    exact hBounded2_raw
  have hSupportMul :=
    mulConstraint_support_subset
      (n := builder1.nextVar)
      (vx := vy) (vy := vx) (vz := vmul)
      hvy_lt1 hvx_lt1 hvmul_lt1
  have hSupport2_raw :=
    Builder.addConstraint_preserve_support
      (st := builder1)
      (c :=
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 })
      hSupport1 hSupportMul
  have hSupport2 :
      SupportOK builder2 := by
    change
      SupportOK
        (Builder.addConstraint builder1
          { A := LinComb.single vy 1
            B := LinComb.single vx 1
            C := LinComb.single vmul 1 })
    exact hSupport2_raw

  have hMulEq :
      builder1.assign vy * builder1.assign vx =
        builder1.assign vmul := by
    calc
      builder1.assign vy * builder1.assign vx
          = boolToRat y * boolToRat x := by
            rw [hvy_assign1, hvx_assign1]
      _ = boolToRat (y && x) := (ZK.boolToRat_and y x).symm
      _ = builder1.assign vmul := by
            rw [← hvmul_assign1]

  have hMulSat :
      Constraint.satisfied builder1.assign
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 } :=
    mul_head_satisfied_of_eq
      (a := builder1.assign) (vx := vy) (vy := vx) (vz := vmul) hMulEq

  have hSat2 :
      System.satisfied builder2.assign (Builder.system builder2) :=
    Builder.addConstraint_preserve_satisfied_mem
      (st := builder1)
      (c :=
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 })
      hSat1 hMulSat

  have hBuilder2_assign :
      builder2.assign = builder1.assign := by
    change
      (Builder.addConstraint builder1
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 }).assign = builder1.assign
    exact Builder.addConstraint_assign _ _
  have hBuilder2_next :
      builder2.nextVar = builder1.nextVar := by
    change
      (Builder.addConstraint builder1
        { A := LinComb.single vy 1
          B := LinComb.single vx 1
          C := LinComb.single vmul 1 }).nextVar = builder1.nextVar
    exact Builder.addConstraint_nextVar _ _

  have hvmul_assign2 :
      builder2.assign vmul = boolToRat (y && x) := by
    have hEq := congrArg (fun f => f vmul) hBuilder2_assign
    exact hEq.trans hvmul_assign1
  have hvmul_bool :
      Constraint.satisfied builder2.assign (boolConstraint vmul) := by
    have hEq :
        builder2.assign vmul * (builder2.assign vmul - 1) = 0 := by
      have h := ZK.boolToRat_sq_sub (y && x)
      calc
        builder2.assign vmul * (builder2.assign vmul - 1)
            = boolToRat (y && x) * (boolToRat (y && x) - 1) := by
                rw [hvmul_assign2]
        _ = 0 := h
    exact
      (boolConstraint_satisfied (assign := builder2.assign) (v := vmul)).2 hEq

  have hBuilder3_assign :
      builder3.assign = builder2.assign := by
    change (recordBoolean builder2 vmul).assign = builder2.assign
    exact Builder.recordBoolean_assign _ _
  have hBuilder3_next :
      builder3.nextVar = builder2.nextVar := by
    change (recordBoolean builder2 vmul).nextVar = builder2.nextVar
    exact Builder.recordBoolean_nextVar _ _

  have hSupport3 :
      SupportOK builder3 :=
    recordBoolean_preserve_support
      (builder := builder2) (v := vmul) hSupport2
      (by
        have : vmul < builder2.nextVar := hBuilder2_next.symm ▸ hvmul_lt1
        exact this)
  have hSat3 :
      System.satisfied builder3.assign (Builder.system builder3) :=
    recordBoolean_preserve_satisfied_mem
      (builder := builder2) (v := vmul) hSat2 hvmul_bool
  have hMatches3 :
      Matches builder3 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches (recordBoolean builder2 vmul)
        (x :: y :: before) (vx :: vy :: vars)
    exact
      recordBoolean_preserve_matches
        (builder := builder2) (v := vmul) hMatches2
  have hBounded3 :
      Bounded builder3 (vx :: vy :: vars) := by
    change
      Bounded (recordBoolean builder2 vmul) (vx :: vy :: vars)
    exact
      recordBoolean_preserve_bounded
        (builder := builder2) (v := vmul) hBounded2

  have hvx_lt3 : vx < builder3.nextVar :=
    hBounded3 vx (by simp)
  have hvy_lt3 : vy < builder3.nextVar :=
    hBounded3 vy (by simp)
  have hvmul_lt3 :
      vmul < builder3.nextVar := by
    have hBase : vmul < builder1.nextVar := hvmul_lt1
    have hStep : vmul < builder2.nextVar :=
      hBuilder2_next.symm ▸ hBase
    exact hBuilder3_next.symm ▸ hStep

  have hvx_assign4 :
      builder4.assign vx = boolToRat x := by
    have hFresh :=
      Builder.fresh_assign_lt
        (st := builder3) (value := boolToRat z)
        (w := vx) (hw := hvx_lt3)
    have hFresh' : builder4.assign vx = builder3.assign vx :=
      hFreshZ_builder ▸ hFresh
    have hAssign3 :
        builder3.assign vx = builder2.assign vx :=
      congrArg (fun f => f vx) hBuilder3_assign
    have hAssign2 :
        builder2.assign vx = builder1.assign vx :=
      congrArg (fun f => f vx) hBuilder2_assign
    have hChain :
        builder3.assign vx = boolToRat x := by
      calc
        builder3.assign vx
            = builder2.assign vx := hAssign3
        _ = builder1.assign vx := hAssign2
        _ = boolToRat x := hvx_assign1
    exact hFresh'.trans hChain

  have hvy_assign4 :
      builder4.assign vy = boolToRat y := by
    have hFresh :=
      Builder.fresh_assign_lt
        (st := builder3) (value := boolToRat z)
        (w := vy) (hw := hvy_lt3)
    have hFresh' : builder4.assign vy = builder3.assign vy :=
      hFreshZ_builder ▸ hFresh
    have hAssign3 :
        builder3.assign vy = builder2.assign vy :=
      congrArg (fun f => f vy) hBuilder3_assign
    have hAssign2 :
        builder2.assign vy = builder1.assign vy :=
      congrArg (fun f => f vy) hBuilder2_assign
    have hChain :
        builder3.assign vy = boolToRat y := by
      calc
        builder3.assign vy
            = builder2.assign vy := hAssign3
        _ = builder1.assign vy := hAssign2
        _ = boolToRat y := hvy_assign1
    exact hFresh'.trans hChain

  have hvmul_assign4 :
      builder4.assign vmul = boolToRat (y && x) := by
    have hFresh :=
      Builder.fresh_assign_lt
        (st := builder3) (value := boolToRat z)
        (w := vmul) (hw := hvmul_lt3)
    have hFresh' : builder4.assign vmul = builder3.assign vmul :=
      hFreshZ_builder ▸ hFresh
    have hAssign3 :
        builder3.assign vmul = builder2.assign vmul :=
      congrArg (fun f => f vmul) hBuilder3_assign
    have hAssign2 :
        builder2.assign vmul = builder1.assign vmul :=
      congrArg (fun f => f vmul) hBuilder2_assign
    have hChain :
        builder3.assign vmul = boolToRat (y && x) := by
      calc
        builder3.assign vmul
            = builder2.assign vmul := hAssign3
        _ = builder1.assign vmul := hAssign2
        _ = boolToRat (y && x) := hvmul_assign1
    exact hFresh'.trans hChain

  have hvz_assign4 :
      builder4.assign vz = boolToRat z := by
    have hAssign :=
      Builder.fresh_assign_self
        (st := builder3) (value := boolToRat z)
    have hAssign' :=
      hFreshZ_builder ▸ hAssign
    exact hFreshZ_v ▸ hAssign'

  have hvz_idx : vz = builder3.nextVar :=
    hFreshZ_v ▸ Builder.fresh_snd (st := builder3) (value := boolToRat z)
  have hbuilder4_next :
      builder4.nextVar = builder3.nextVar + 1 :=
    hFreshZ_builder ▸
      Builder.fresh_nextVar (st := builder3) (value := boolToRat z)

  have hMatches4 :
      Matches builder4 (x :: y :: before) (vx :: vy :: vars) := by
    have h :=
      matches_fresh_preserve
        (builder := builder3)
        (stack := x :: y :: before)
        (vars := vx :: vy :: vars)
        (value := boolToRat z) hMatches3 hBounded3
    exact hFreshZ_builder ▸ h
  have hBounded4 :
      Bounded builder4 (vx :: vy :: vars) := by
    have h :=
      Builder.fresh_preserve_bounded
        (st := builder3) (value := boolToRat z)
        (vars := vx :: vy :: vars) hBounded3
    exact hFreshZ_builder ▸ h
  have hSupport4 :
      SupportOK builder4 := by
    have h :=
      Builder.fresh_preserve_support
        (st := builder3) (value := boolToRat z) hSupport3
    exact hFreshZ_builder ▸ h
  have hSat4 :
      System.satisfied builder4.assign (Builder.system builder4) :=
    Builder.fresh_preserve_satisfied_mem
      (st := builder3) (value := boolToRat z) hSupport3 hSat3

  have hvz_lt4 :
      vz < builder4.nextVar := by
    have hBase : builder3.nextVar < builder3.nextVar + 1 :=
      Nat.lt_succ_self builder3.nextVar
    have hStep : builder3.nextVar < builder4.nextVar :=
      hbuilder4_next.symm ▸ hBase
    exact hvz_idx.symm ▸ hStep
  have hvx_lt4 :
      vx < builder4.nextVar := by
    have hBase : vx < builder3.nextVar + 1 :=
      Nat.lt_succ_of_lt hvx_lt3
    exact hbuilder4_next.symm ▸ hBase
  have hvy_lt4 :
      vy < builder4.nextVar := by
    have hBase : vy < builder3.nextVar + 1 :=
      Nat.lt_succ_of_lt hvy_lt3
    exact hbuilder4_next.symm ▸ hBase
  have hvmul_lt4 :
      vmul < builder4.nextVar := by
    have hBase : vmul < builder3.nextVar + 1 :=
      Nat.lt_succ_of_lt hvmul_lt3
    exact hbuilder4_next.symm ▸ hBase

  have hLinSubset :
      (linhead_imp vz vx vy vmul).support ⊆
        Finset.range builder4.nextVar := by
    refine subset_trans (linhead_imp_support vz vx vy vmul) ?_
    exact four_var_support_subset
      (n := builder4.nextVar)
      hvz_lt4 hvx_lt4 hvy_lt4 hvmul_lt4

  have hSupport5 :
      SupportOK builder5 := by
    have hConstraintSubset :
        Constraint.support eqImp ⊆ Finset.range builder4.nextVar := by
      intro w hw
      have hSupportEq :
          Constraint.support eqImp =
            (linhead_imp vz vx vy vmul).support := by
        dsimp [eqImp, eqConstraint, Constraint.support]
        rw [
          LinComb.support_ofConst (1 : ℚ),
          LinComb.support_ofConst (0 : ℚ),
          Finset.union_empty,
          Finset.union_empty]
      have hw' :
          w ∈ (linhead_imp vz vx vy vmul).support :=
        hSupportEq ▸ hw
      exact hLinSubset hw'
    have h :=
      Builder.addConstraint_preserve_support
        (st := builder4) (c := eqImp) hSupport4 hConstraintSubset
    change
      SupportOK (Builder.addConstraint builder4 eqImp)
    exact h
  have hMulClosed :
      builder4.assign vmul =
        builder4.assign vx * builder4.assign vy := by
    calc
      builder4.assign vmul
          = boolToRat (y && x) := hvmul_assign4
      _ = boolToRat y * boolToRat x := ZK.boolToRat_and y x
      _ = builder4.assign vy * builder4.assign vx := by
            rw [hvy_assign4, hvx_assign4]
      _ = builder4.assign vx * builder4.assign vy := by
            rw [mul_comm]
  have hImpClosed :
      builder4.assign vz =
        1 - builder4.assign vy + builder4.assign vy * builder4.assign vx := by
    calc
      builder4.assign vz
          = boolToRat z := hvz_assign4
      _ = boolToRat ((! y) || x) := rfl
      _ = 1 - boolToRat y + boolToRat y * boolToRat x :=
            ZK.boolToRat_imp y x
      _ = 1 - builder4.assign vy + builder4.assign vy * builder4.assign vx := by
            rw [hvy_assign4, hvx_assign4]

  have hEqConstraint :
      Constraint.satisfied builder4.assign eqImp :=
    head_satisfied_imp
      (a := builder4.assign) (vx := vx) (vy := vy)
      (vmul := vmul) (vz := vz) hMulClosed hImpClosed

  have hMatches5 :
      Matches builder5 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches (Builder.addConstraint builder4 eqImp)
        (x :: y :: before) (vx :: vy :: vars)
    exact
      addConstraint_preserve_matches hMatches4 eqImp
  have hBounded5 :
      Bounded builder5 (vx :: vy :: vars) := by
    change
      Bounded (Builder.addConstraint builder4 eqImp) (vx :: vy :: vars)
    exact
      addConstraint_preserve_bounded hBounded4 eqImp
  have hSat5 :
      System.satisfied builder5.assign (Builder.system builder5) :=
    Builder.addConstraint_preserve_satisfied_mem
      (st := builder4) (c := eqImp) hSat4 hEqConstraint

  have hBuilder5_assign :
      builder5.assign = builder4.assign := by
    change (Builder.addConstraint builder4 eqImp).assign = builder4.assign
    exact Builder.addConstraint_assign _ _
  have hBuilder5_next :
      builder5.nextVar = builder4.nextVar := by
    change (Builder.addConstraint builder4 eqImp).nextVar = builder4.nextVar
    exact Builder.addConstraint_nextVar _ _

  have hvz_assign5 :
      builder5.assign vz = boolToRat z := by
    have h := congrArg (fun f => f vz) hBuilder5_assign
    exact h.trans hvz_assign4
  have hBoolZ :
      Constraint.satisfied builder5.assign (boolConstraint vz) := by
    have hEq :
        builder5.assign vz * (builder5.assign vz - 1) = 0 := by
      have h := ZK.boolToRat_sq_sub z
      calc
        builder5.assign vz * (builder5.assign vz - 1)
            = boolToRat z * (boolToRat z - 1) := by
                rw [hvz_assign5]
        _ = 0 := h
    exact
      (boolConstraint_satisfied (assign := builder5.assign) (v := vz)).2 hEq

  have hSupport6 :
      SupportOK builder6 :=
    recordBoolean_preserve_support
      (builder := builder5) (v := vz) hSupport5
      (by
        have : vz < builder5.nextVar := hBuilder5_next.symm ▸ hvz_lt4
        exact this)
  have hSat6 :
      System.satisfied builder6.assign (Builder.system builder6) :=
    recordBoolean_preserve_satisfied_mem
      (builder := builder5) (v := vz) hSat5 hBoolZ
  have hMatches6 :
      Matches builder6 (x :: y :: before) (vx :: vy :: vars) := by
    change
      Matches (recordBoolean builder5 vz)
        (x :: y :: before) (vx :: vy :: vars)
    exact
      recordBoolean_preserve_matches
        (builder := builder5) (v := vz) hMatches5
  have hBounded6 :
      Bounded builder6 (vx :: vy :: vars) := by
    change
      Bounded (recordBoolean builder5 vz) (vx :: vy :: vars)
    exact
      recordBoolean_preserve_bounded
        (builder := builder5) (v := vz) hBounded5

  have hMatchesTail6 :
      Matches builder6 before vars :=
    matches_tail_tail hMatches6

  have hBuilder6_assign :
      builder6.assign = builder5.assign := by
    change (recordBoolean builder5 vz).assign = builder5.assign
    exact Builder.recordBoolean_assign _ _
  have hBuilder6_next :
      builder6.nextVar = builder5.nextVar := by
    change (recordBoolean builder5 vz).nextVar = builder5.nextVar
    exact Builder.recordBoolean_nextVar _ _

  have hvz_assign6 :
      builder6.assign vz = boolToRat z := by
    have h := congrArg (fun f => f vz) hBuilder6_assign
    exact h.trans hvz_assign5
  have hMatchesFinal :
      Matches builder6 (z :: before) (vz :: vars) :=
    List.Forall₂.cons hvz_assign6.symm hMatchesTail6

  have hBoundedTail6 :
      Bounded builder6 vars :=
    Bounded.tail_tail hBounded6
  have hnext_builder6 :
      builder6.nextVar = builder4.nextVar :=
    hBuilder6_next.trans hBuilder5_next
  have hBoundedFinal :
      Bounded builder6 (vz :: vars) := by
    intro w hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst hw
      have hz := hvz_lt4
      exact hnext_builder6.symm ▸ hz
    · exact hBoundedTail6 w hw

  exact ⟨hMatchesFinal, ⟨hBoundedFinal, ⟨hSupport6, hSat6⟩⟩⟩
private def compileStep {n : ℕ} (ρ : Env n)
    (instr : Instr n) (before after : Stack)
    (stackVars : List Var) (builder : Builder) :
    Builder × List Var := by
  classical
  cases instr with
  | pushTop =>
      let (builder', v) := pushConst builder 1
      exact (builder', v :: stackVars)
  | pushBot =>
      let (builder', v) := pushConst builder 0
      exact (builder', v :: stackVars)
  | pushVar idx =>
      let val := boolToRat (ρ idx)
      let (builder', v) := pushConst builder val
      exact (builder', v :: stackVars)
  | applyAnd =>
      match before, after, stackVars with
      | _x :: _y :: _, z :: _, vx :: vy :: rest =>
          let (builder1, vz) := Builder.fresh builder (boolToRat z)
          let builder2 :=
            Builder.addConstraint builder1
              { A := LinComb.single vx 1
                B := LinComb.single vy 1
                C := LinComb.single vz 1 }
          let builder3 := recordBoolean builder2 vz
          exact (builder3, vz :: rest)
      | _, _, _ =>
          exact (builder, stackVars)
  | applyOr =>
      match before, after, stackVars with
      | x :: y :: _, z :: _, vx :: vy :: rest =>
          let mulVal := boolToRat (y && x)
          let (builder1, vmul) := Builder.fresh builder mulVal
          let builder2 :=
            Builder.addConstraint builder1
              { A := LinComb.single vy 1
                B := LinComb.single vx 1
                C := LinComb.single vmul 1 }
          let builder3 := recordBoolean builder2 vmul
          let (builder4, vz) := Builder.fresh builder3 (boolToRat z)
          let builder5 :=
            Builder.addConstraint builder4
              (eqConstraint (linhead_or vz vx vy vmul) (LinComb.ofConst 0))
          let builder6 := recordBoolean builder5 vz
          exact (builder6, vz :: rest)
      | _, _, _ =>
          exact (builder, stackVars)
  | applyImp =>
      match before, after, stackVars with
      | x :: y :: _, z :: _, vx :: vy :: rest =>
          let mulVal := boolToRat (y && x)
          let (builder1, vmul) := Builder.fresh builder mulVal
          let builder2 :=
            Builder.addConstraint builder1
              { A := LinComb.single vy 1
                B := LinComb.single vx 1
                C := LinComb.single vmul 1 }
          let builder3 := recordBoolean builder2 vmul
          let (builder4, vz) := Builder.fresh builder3 (boolToRat z)
          let builder5 :=
            Builder.addConstraint builder4
              (eqConstraint (linhead_imp vz vx vy vmul) (LinComb.ofConst 0))
          let builder6 := recordBoolean builder5 vz
          exact (builder6, vz :: rest)
      | _, _, _ =>
          exact (builder, stackVars)

-- Length contradictions helpers placed before usage in compileStep_strong
private lemma lenConsCons_eq_lenNil_false {α β}
    (x y : α) (xs : List α) :
    ((x :: y :: xs).length = ([] : List β).length) → False := by
  intro h
  -- rewrite length equalities explicitly, then contradict with succ_ne_zero
  have h2 := h
  rw [List.length_cons] at h2
  rw [List.length_cons] at h2
  exact (Nat.succ_ne_zero _) h2

private lemma lenConsCons_eq_lenSingleton_false {α β}
    (x y : α) (xs : List α) (z : β) :
    ((x :: y :: xs).length = ([z] : List β).length) → False := by
  intro h
  -- rewrite length equalities explicitly; inject and contradict
  have h2 := h
  rw [List.length_cons] at h2
  rw [List.length_cons] at h2
  have : Nat.succ xs.length = 0 := Nat.succ.inj h2
  exact (Nat.succ_ne_zero _) this

lemma compileStep_strong {n : ℕ} (ρ : Env n)
    {instr : Instr n} {before after : Stack}
    {stackVars : List Var} {builder : Builder}
    (hStrong : StrongInvariant builder before stackVars)
    (hStep : after = BoolLens.step ρ instr before) :
    StrongInvariant
      (compileStep ρ instr before after stackVars builder).1
      after
      (compileStep ρ instr before after stackVars builder).2 := by
  classical
  cases instr with
  | pushTop =>
      have hAfter := hStep
      simp [BoolLens.step] at hAfter
      subst hAfter
      have hRes :=
        pushConst_strong
          (builder := builder) (stack := before) (vars := stackVars)
          (hStrong := hStrong) (value := 1) (b := true)
          (hvalue := by simp)
      -- prefer simp at pattern over simpa using
      have hRes' := hRes
      simp at hRes'
      exact hRes'
  | pushBot =>
      have hAfter := hStep
      simp [BoolLens.step] at hAfter
      subst hAfter
      have hRes :=
        pushConst_strong
          (builder := builder) (stack := before) (vars := stackVars)
          (hStrong := hStrong) (value := 0) (b := false)
          (hvalue := by simp)
      have hRes' := hRes
      simp at hRes'
      exact hRes'
  | pushVar idx =>
      have hAfter := hStep
      simp [BoolLens.step] at hAfter
      subst hAfter
      have hRes :=
        pushConst_strong
          (builder := builder) (stack := before) (vars := stackVars)
          (hStrong := hStrong) (value := boolToRat (ρ idx)) (b := ρ idx)
          (hvalue := by rfl)
      have hRes' := hRes
      simp at hRes'
      exact hRes'
  | applyAnd =>
      cases before with
      | nil =>
          have hAfter : after = [] := by
            simpa [BoolLens.step] using hStep
          subst hAfter
          simpa [compileStep] using hStrong
      | cons x before₁ =>
          cases before₁ with
          | nil =>
              have hAfter : after = [x] := by
                simpa [BoolLens.step] using hStep
              subst hAfter
              simpa [compileStep] using hStrong
          | cons y beforeTail =>
              cases stackVars with
              | nil =>
                  have hlen :=
                    matches_length_eq (StrongInvariant.matches_ hStrong)
                  have : False :=
                    lenConsCons_eq_lenNil_false x y beforeTail (α:=Bool) (β:=Var) hlen
                  exact this.elim
              | cons vx stackVars₁ =>
                  cases stackVars₁ with
                  | nil =>
                      have hlen :=
                        matches_length_eq (StrongInvariant.matches_ hStrong)
                      have : False :=
                        lenConsCons_eq_lenSingleton_false x y beforeTail vx (α:=Bool) (β:=Var) hlen
                      exact this.elim
                  | cons vy vars =>
                      have hStrongXY :
                          StrongInvariant builder (x :: y :: beforeTail)
                            (vx :: vy :: vars) := by
                        simpa using hStrong
                      have hMatchesXY :=
                        StrongInvariant.matches_ hStrongXY
                      have hxEq :
                          boolToRat x = builder.assign vx :=
                        matches_cons_head
                          (builder := builder)
                          (stack := y :: beforeTail)
                          (v := vx) (vars := vy :: vars) hMatchesXY
                      have hTailMatches :
                          Matches builder (y :: beforeTail) (vy :: vars) :=
                        matches_cons_tail
                          (builder := builder)
                          (b := x) (stack := y :: beforeTail)
                          (v := vx) (vars := vy :: vars) hMatchesXY
                      have hyEq :
                          boolToRat y = builder.assign vy :=
                        matches_cons_head
                          (builder := builder)
                          (stack := beforeTail)
                          (v := vy) (vars := vars) hTailMatches
                      have hvxB :
                          builder.assign vx = 0 ∨ builder.assign vx = 1 := by
                        cases x <;> simp [boolToRat, hxEq.symm]
                      have hvyB :
                          builder.assign vy = 0 ∨ builder.assign vy = 1 := by
                        cases y <;> simp [boolToRat, hyEq.symm]
                      have hAfterVal :
                          after = (y && x) :: beforeTail := by
                        simpa [BoolLens.step, BoolLens.applyBinary_cons_cons] using hStep
                      subst hAfterVal
                      have hRes :=
                        applyAnd_strong
                          (builder := builder)
                          (x := x) (y := y)
                          (before := beforeTail)
                          (vx := vx) (vy := vy) (vars := vars)
                          (hStrong := hStrongXY)
                          (hvxB := hvxB) (hvyB := hvyB)
                      simpa [compileStep] using hRes
  | applyOr =>
      cases before with
      | nil =>
          have hAfter : after = [] := by
            simpa [BoolLens.step] using hStep
          subst hAfter
          simpa [compileStep] using hStrong
      | cons x before₁ =>
          cases before₁ with
          | nil =>
              have hAfter : after = [x] := by
                simpa [BoolLens.step] using hStep
              subst hAfter
              simpa [compileStep] using hStrong
          | cons y beforeTail =>
              cases stackVars with
              | nil =>
                  have hlen :=
                    matches_length_eq (StrongInvariant.matches_ hStrong)
                  have : False :=
                    lenConsCons_eq_lenNil_false x y beforeTail (α:=Bool) (β:=Var) hlen
                  exact this.elim
              | cons vx stackVars₁ =>
                  cases stackVars₁ with
                  | nil =>
                      have hlen :=
                        matches_length_eq (StrongInvariant.matches_ hStrong)
                      have : False :=
                        lenConsCons_eq_lenSingleton_false x y beforeTail vx (α:=Bool) (β:=Var) hlen
                      exact this.elim
                  | cons vy vars =>
                      have hStrongXY :
                          StrongInvariant builder (x :: y :: beforeTail)
                            (vx :: vy :: vars) := by
                        simpa using hStrong
                      have hMatchesXY :=
                        StrongInvariant.matches_ hStrongXY
                      have hxEq :
                          boolToRat x = builder.assign vx :=
                        matches_cons_head
                          (builder := builder)
                          (stack := y :: beforeTail)
                          (v := vx) (vars := vy :: vars) hMatchesXY
                      have hTailMatches :
                          Matches builder (y :: beforeTail) (vy :: vars) :=
                        matches_cons_tail
                          (builder := builder)
                          (b := x) (stack := y :: beforeTail)
                          (v := vx) (vars := vy :: vars) hMatchesXY
                      have hyEq :
                          boolToRat y = builder.assign vy :=
                        matches_cons_head
                          (builder := builder)
                          (stack := beforeTail)
                          (v := vy) (vars := vars) hTailMatches
                      have hvxB :
                          builder.assign vx = 0 ∨ builder.assign vx = 1 := by
                        cases x <;> simp [boolToRat, hxEq.symm]
                      have hvyB :
                          builder.assign vy = 0 ∨ builder.assign vy = 1 := by
                        cases y <;> simp [boolToRat, hyEq.symm]
                      have hAfterVal :
                          after = (y || x) :: beforeTail := by
                        simpa [BoolLens.step, BoolLens.applyBinary_cons_cons] using hStep
                      subst hAfterVal
                      have hRes :=
                        applyOr_strong
                          (builder := builder)
                          (x := x) (y := y)
                          (before := beforeTail)
                          (vx := vx) (vy := vy) (vars := vars)
                          (hStrong := hStrongXY)
                          (_hvxB := hvxB) (_hvyB := hvyB)
                      simpa [compileStep] using hRes
  | applyImp =>
      cases before with
      | nil =>
          have hAfter : after = [] := by
            simpa [BoolLens.step] using hStep
          subst hAfter
          simpa [compileStep] using hStrong
      | cons x before₁ =>
          cases before₁ with
          | nil =>
              have hAfter : after = [x] := by
                simpa [BoolLens.step] using hStep
              subst hAfter
              simpa [compileStep] using hStrong
          | cons y beforeTail =>
              cases stackVars with
              | nil =>
                  have hlen :=
                    matches_length_eq (StrongInvariant.matches_ hStrong)
                  have : False :=
                    lenConsCons_eq_lenNil_false x y beforeTail (α:=Bool) (β:=Var) hlen
                  exact this.elim
              | cons vx stackVars₁ =>
                  cases stackVars₁ with
                  | nil =>
                      have hlen :=
                        matches_length_eq (StrongInvariant.matches_ hStrong)
                      have : False :=
                        lenConsCons_eq_lenSingleton_false x y beforeTail vx (α:=Bool) (β:=Var) hlen
                      exact this.elim
                  | cons vy vars =>
                      have hStrongXY :
                          StrongInvariant builder (x :: y :: beforeTail)
                            (vx :: vy :: vars) := by
                        simpa using hStrong
                      have hMatchesXY :=
                        StrongInvariant.matches_ hStrongXY
                      have hxEq :
                          boolToRat x = builder.assign vx :=
                        matches_cons_head
                          (builder := builder)
                          (stack := y :: beforeTail)
                          (v := vx) (vars := vy :: vars) hMatchesXY
                      have hTailMatches :
                          Matches builder (y :: beforeTail) (vy :: vars) :=
                        matches_cons_tail
                          (builder := builder)
                          (b := x) (stack := y :: beforeTail)
                          (v := vx) (vars := vy :: vars) hMatchesXY
                      have hyEq :
                          boolToRat y = builder.assign vy :=
                        matches_cons_head
                          (builder := builder)
                          (stack := beforeTail)
                          (v := vy) (vars := vars) hTailMatches
                      have hvxB :
                          builder.assign vx = 0 ∨ builder.assign vx = 1 := by
                        cases x <;> simp [boolToRat, hxEq.symm]
                      have hvyB :
                          builder.assign vy = 0 ∨ builder.assign vy = 1 := by
                        cases y <;> simp [boolToRat, hyEq.symm]
                      have hAfterVal :
                          after = ((! y) || x) :: beforeTail := by
                        simpa [BoolLens.step, BoolLens.applyBinary_cons_cons] using hStep
                      subst hAfterVal
                      have hRes :=
                        applyImp_strong
                          (builder := builder)
                          (x := x) (y := y)
                          (before := beforeTail)
                          (vx := vx) (vy := vy) (vars := vars)
                          (hStrong := hStrongXY)
                          (_hvxB := hvxB) (_hvyB := hvyB)
                      simpa [compileStep] using hRes
private def compileSteps {n : ℕ} (ρ : Env n)
    (prog : Program n) (trace : List Stack)
    (stackVars : List Var) (builder : Builder) :
    Builder × List Var :=
  match prog, trace with
  | [], _ => (builder, stackVars)
  | _, [] => (builder, stackVars)
  | instr :: prog', before :: trace' =>
      match trace' with
      | [] => (builder, stackVars)
      | after :: traceTail =>
          let (builder', stackVars') :=
            compileStep ρ instr before after stackVars builder
          compileSteps ρ prog' (after :: traceTail) stackVars' builder'

lemma compileSteps_strong {n : ℕ} (ρ : Env n)
    {prog : Program n} {stack : Stack}
    {stackVars : List Var} {builder : Builder}
    (hStrong : StrongInvariant builder stack stackVars) :
    StrongInvariant
      (compileSteps ρ prog (BoolLens.traceFrom ρ prog stack) stackVars builder).1
      (BoolLens.exec ρ prog stack)
      (compileSteps ρ prog (BoolLens.traceFrom ρ prog stack) stackVars builder).2 := by
  classical
  induction prog generalizing stack stackVars builder with
  | nil =>
      simpa [compileSteps, BoolLens.traceFrom_nil, BoolLens.exec] using hStrong
  | cons instr prog ih =>
      have hStepStrong :=
        compileStep_strong (ρ := ρ) (instr := instr)
          (before := stack)
          (after := BoolLens.step ρ instr stack)
          (stackVars := stackVars) (builder := builder)
          hStrong (by rfl)
      cases hStepResult :
          compileStep ρ instr stack (BoolLens.step ρ instr stack) stackVars builder with
      | mk builder' stackVars' =>
          have hStrong' :
              StrongInvariant builder'
                (BoolLens.step ρ instr stack) stackVars' := by
            simpa [hStepResult] using hStepStrong
          have hRec :=
            ih (builder := builder') (stack := BoolLens.step ρ instr stack)
              (stackVars := stackVars') hStrong'
          obtain ⟨traceTail, hTraceTail⟩ :=
            BoolLens.traceFrom_cons_head (ρ := ρ)
              (prog := prog) (stk := BoolLens.step ρ instr stack)
          simpa [BoolLens.exec_cons, BoolLens.traceFrom_cons, compileSteps,
            hStepResult, hTraceTail]
            using hRec

/-! Public wrappers from empty stack to expose strong invariant results. -/

def compileTraceToR1CSFromEmpty {n : ℕ} (ρ : Env n)
    (prog : Program n) : Builder × List Var :=
  compileSteps ρ prog (BoolLens.traceFrom ρ prog []) [] {}

lemma compileTraceToR1CSFromEmpty_strong {n : ℕ} (ρ : Env n)
    {prog : Program n} :
    StrongInvariant
      (compileTraceToR1CSFromEmpty ρ prog).1
      (BoolLens.exec ρ prog [])
      (compileTraceToR1CSFromEmpty ρ prog).2 := by
  classical
  simpa [compileTraceToR1CSFromEmpty]
    using compileSteps_strong (ρ := ρ)
      (prog := prog) (stack := [])
      (stackVars := []) (builder := {}) strongInvariant_empty

lemma compileTraceToR1CSFromEmpty_satisfied {n : ℕ} (ρ : Env n)
    {prog : Program n} :
    System.satisfied (compileTraceToR1CSFromEmpty ρ prog).1.assign
      (Builder.system (compileTraceToR1CSFromEmpty ρ prog).1) := by
  classical
  exact (StrongInvariant.satisfied_
    (compileTraceToR1CSFromEmpty_strong (ρ := ρ) (prog := prog)))

lemma compileTraceToR1CSFromEmpty_supportOK {n : ℕ} (ρ : Env n)
    {prog : Program n} :
    SupportOK (compileTraceToR1CSFromEmpty ρ prog).1 := by
  classical
  exact (StrongInvariant.support_
    (compileTraceToR1CSFromEmpty_strong (ρ := ρ) (prog := prog)))

lemma compileTraceToR1CSFromEmpty_matches {n : ℕ} (ρ : Env n)
    {prog : Program n} :
    Matches (compileTraceToR1CSFromEmpty ρ prog).1
      (BoolLens.exec ρ prog [])
      (compileTraceToR1CSFromEmpty ρ prog).2 := by
  classical
  exact (StrongInvariant.matches_
    (compileTraceToR1CSFromEmpty_strong (ρ := ρ) (prog := prog)))

lemma compileSteps_strong_empty {n : ℕ} (ρ : Env n)
    (prog : Program n) :
    StrongInvariant
      (compileSteps ρ prog (BoolLens.traceFrom ρ prog []) [] {}).1
      (BoolLens.exec ρ prog [])
      (compileSteps ρ prog (BoolLens.traceFrom ρ prog []) [] {}).2 := by
  simpa using
    (compileSteps_strong (ρ := ρ)
      (prog := prog) (stack := []) (stackVars := []) (builder := {})
      strongInvariant_empty)

lemma compile_strong {n : ℕ} (φ : Form n) (ρ : Env n) :
    StrongInvariant
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).1
      (BoolLens.exec ρ (Form.compile φ) [])
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).2 := by
  simpa using
    (compileSteps_strong_empty (ρ := ρ) (prog := Form.compile φ))

lemma compile_invariant {n : ℕ} (φ : Form n) (ρ : Env n) :
    Invariant
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).1
      (BoolLens.exec ρ (Form.compile φ) [])
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).2 := by
  classical
  have hStrong :=
    compile_strong (φ := φ) (ρ := ρ)
  obtain ⟨hMatches, hBounded, -, -⟩ := hStrong
  exact
    ⟨hMatches, hBounded, matches_length_eq hMatches⟩

lemma compile_matches {n : ℕ} (φ : Form n) (ρ : Env n) :
    Matches
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).1
      (BoolLens.exec ρ (Form.compile φ) [])
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).2 :=
  (compile_strong (φ := φ) (ρ := ρ)).1

/-- Compile a Boolean form/environment pair into R1CS constraints and witness. -/
def compile {n : ℕ} (φ : Form n) (ρ : Env n) : Compiled := by
  classical
  let prog := Form.compile φ
  let trace := BoolLens.traceFrom ρ prog []
  let (builder, stackVars) :=
    compileSteps (ρ := ρ) prog trace [] {}
  let outputVar := stackVars.headD 0
  exact
    { system := { constraints := builder.constraints.reverse }
      assignment := builder.assign
      output := outputVar }

@[simp] lemma compile_system_constraints {n : ℕ} (φ : Form n) (ρ : Env n) :
    (compile φ ρ).system.constraints =
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).1.constraints.reverse := by
  simp [compile]

@[simp] lemma compile_assignment {n : ℕ} (φ : Form n) (ρ : Env n) :
    (compile φ ρ).assignment =
      (compileSteps (ρ := ρ) (Form.compile φ)
        (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).1.assign := by
  simp [compile]

lemma compile_support_subset {n : ℕ} (φ : Form n) (ρ : Env n) :
    System.support (compile φ ρ).system ⊆
      Finset.range
        ((compileSteps (ρ := ρ) (Form.compile φ)
          (BoolLens.traceFrom ρ (Form.compile φ) []) [] {}).1).nextVar := by
  classical
  let prog := Form.compile φ
  let trace := BoolLens.traceFrom ρ prog []
  let result := compileSteps (ρ := ρ) prog trace [] {}
  let builder := result.1
  have hSupport :=
    StrongInvariant.support_reverse_subset
      (compile_strong (φ := φ) (ρ := ρ))
  have hSupport' :
      System.support { constraints := builder.constraints.reverse } ⊆
        Finset.range builder.nextVar := by
    simpa [prog, trace, result, builder] using hSupport
  simpa [compile, prog, trace, result, builder,
    compile_system_constraints] using hSupport'

end R1CSBool
end ZK
end Crypto
end HeytingLean
