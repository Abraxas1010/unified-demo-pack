import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace ZK
namespace Rename

/-- Rename variables in a linear combination by mapping indices through `σ`. -/
def linComb (σ : Var → Var) (lc : LinComb) : LinComb :=
  { const := lc.const, terms := lc.terms.map (fun (p : Var × ℚ) => (σ p.1, p.2)) }

@[simp]
lemma eval_linComb (σ : Var → Var) (a : Var → ℚ) (lc : LinComb) :
    LinComb.eval (linComb σ lc) a = LinComb.eval lc (fun v => a (σ v)) := by
  classical
  unfold LinComb.eval linComb
  revert a
  generalize h : lc.terms = ts
  revert lc
  induction ts with
  | nil =>
      intro lc h a; simp [h]
  | @cons term tail ih =>
      intro lc h a; cases term with
      | mk v c =>
          -- peel one term, then apply IH with updated constant and tail
          have h' : ({ const := lc.const + c * a (σ v), terms := tail } : LinComb).terms = tail := rfl
          have := ih (({ const := lc.const + c * a (σ v), terms := tail } : LinComb)) h' a
          simp [h, this]

/-- Rename variables in a constraint via `σ`. -/
def constraint (σ : Var → Var) (c : Constraint) : Constraint :=
  { A := linComb σ c.A, B := linComb σ c.B, C := linComb σ c.C }

@[simp]
lemma satisfied_constraint (σ : Var → Var) (a : Var → ℚ) (c : Constraint) :
    Constraint.satisfied a (constraint σ c) ↔ Constraint.satisfied (fun v => a (σ v)) c := by
  classical
  unfold Constraint.satisfied constraint
  simp [eval_linComb]

/-- Rename variables in every constraint of a system via `σ`. -/
def system (σ : Var → Var) (sys : System) : System :=
  { constraints := sys.constraints.map (constraint σ) }

@[simp]
lemma satisfied_system (σ : Var → Var) (a : Var → ℚ) (sys : System) :
    System.satisfied a (system σ sys) ↔ System.satisfied (fun v => a (σ v)) sys := by
  classical
  unfold System.satisfied system
  constructor
  · intro h c hc
    have hc' : constraint σ c ∈ (List.map (constraint σ) sys.constraints) := by
      simpa using List.mem_map.mpr ⟨c, hc, rfl⟩
    have hsat : Constraint.satisfied a (constraint σ c) := h hc'
    exact (satisfied_constraint σ a c).1 hsat
  · intro h d hd
    rcases List.mem_map.1 hd with ⟨c, hc, rfl⟩
    have hsat' : Constraint.satisfied (fun v => a (σ v)) c := h hc
    exact (satisfied_constraint σ a c).2 hsat'

end Rename
end ZK
end Crypto
end HeytingLean
