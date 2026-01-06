import HeytingLean.Crypto.Lattice.RecoveryViews
import HeytingLean.Crypto.Lattice.Rings

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Ring-shaped carriers and a bridge back to coefficient-vector MLWE (v0.9 → v1.1)

This module introduces a ring-shaped MLWE recovery view over the standard cyclotomic-style ring
`R_q = (ZMod q)[X] ⧸ ⟨X^n + 1⟩` from `HeytingLean.Crypto.Lattice.Rings`.

It also provides a concrete `Reduction.BridgeData` instance showing how a solver for the ring-shaped
view can be turned into a solver for the existing (statement-first) coefficient-vector `MLWEView`.

This is **not** a cryptographic claim; it is a statement-level bridge between two recovery views
once an explicit embedding is chosen.
-/

open scoped Classical BigOperators Polynomial

namespace RingReductions

/-- View-level ring parameters induced from `MLWEParams`. -/
def cycloOf (P : MLWEParams) : CycloParams :=
  { n := P.n, q := P.q }

abbrev Rq (P : MLWEParams) : Type :=
  Rings.Rq (cycloOf P)

abbrev RModVec (P : MLWEParams) : Type :=
  Fin P.k → Rq P

abbrev RModMat (P : MLWEParams) : Type :=
  Matrix (Fin P.k) (Fin P.k) (Rq P)

structure RMLWEInstance (P : MLWEParams) where
  A : RModMat P
  b : RModVec P

noncomputable instance (P : MLWEParams) : Inhabited (RMLWEInstance P) :=
  ⟨{ A := 0, b := 0 }⟩

structure RMLWESecret (P : MLWEParams) where
  inst : RMLWEInstance P
  s : RModVec P
  e : RModVec P

noncomputable instance (P : MLWEParams) : Inhabited (RMLWESecret P) :=
  ⟨{ inst := default, s := 0, e := 0 }⟩

def RMLWEView (P : MLWEParams) : RecoveryView (RMLWESecret P) where
  Pub := RMLWEInstance P
  encode := fun s => s.inst

noncomputable def polyAsPolynomial (P : MLWEParams) (v : Poly P.n P.q) :
    Rings.Poly (cycloOf P) :=
  ∑ i : Fin P.n, Polynomial.C (v i) * (Polynomial.X ^ (i : Nat))

noncomputable def polyToRq (P : MLWEParams) (v : Poly P.n P.q) : Rq P :=
  Rings.mkRq (cycloOf P) (polyAsPolynomial P v)

/-- The Kyber-style modulus polynomial `X^n + 1` for the induced cyclotomic parameters. -/
noncomputable def modulusPoly (P : MLWEParams) : Rings.Poly (cycloOf P) :=
  Rings.modulusPoly (cycloOf P)

private theorem modulusPoly_monic (P : MLWEParams) (hn : P.n ≠ 0) : (modulusPoly P).Monic := by
  have h :=
    (Polynomial.monic_X_pow_add_C (R := Rings.Base (cycloOf P))
      (a := (1 : Rings.Base (cycloOf P))) hn)
  simpa [modulusPoly, Rings.modulusPoly, cycloOf] using h

private noncomputable def normalize (P : MLWEParams) : Rings.Poly (cycloOf P) → Rings.Poly (cycloOf P) :=
  fun f => f %ₘ modulusPoly P

private noncomputable def polyCoeffs (P : MLWEParams) : Rings.Poly (cycloOf P) → Poly P.n P.q :=
  fun f i => (normalize P f).coeff (i : Nat)

/-- Extract a coefficient-vector from a quotient-ring element by:
1. choosing `Quotient.out` representative;
2. normalizing by `modByMonic (X^n + 1)`; and
3. reading coefficients `0..n-1`. -/
noncomputable def rqCoeffs (P : MLWEParams) : Rq P → Poly P.n P.q :=
  fun x => polyCoeffs P (Quotient.out x)

private theorem coeff_polyAsPolynomial (P : MLWEParams) (v : Poly P.n P.q) (i : Fin P.n) :
    (polyAsPolynomial P v).coeff (i : Nat) = v i := by
  classical
  have hterm : ∀ b : Fin P.n,
      (Polynomial.C (v b) * Polynomial.X ^ (b : Nat)).coeff (i : Nat) =
        (if (i : Nat) = (b : Nat) then v b else 0) := by
    intro b
    simp
  simp [polyAsPolynomial, hterm]
  have hnat : ∀ b : Fin P.n, ((i : Nat) = (b : Nat)) ↔ i = b := by
    intro b
    simp [Fin.ext_iff]
  simp [hnat]

private theorem polyAsPolynomial_degree_lt (P : MLWEParams) (v : Poly P.n P.q) :
    Polynomial.degree (polyAsPolynomial P v) < P.n := by
  simpa [polyAsPolynomial] using (Polynomial.degree_sum_fin_lt (f := fun i : Fin P.n => v i))

private theorem polyAsPolynomial_modByMonic (P : MLWEParams) (hn : P.n ≠ 0) (v : Poly P.n P.q) :
    (polyAsPolynomial P v) %ₘ modulusPoly P = polyAsPolynomial P v := by
  classical
  rcases subsingleton_or_nontrivial (Rings.Base (cycloOf P)) with hsub | hnon
  · haveI : Subsingleton (Rings.Base (cycloOf P)) := hsub
    haveI : Subsingleton (Rings.Poly (cycloOf P)) := by infer_instance
    exact Subsingleton.elim _ _
  · haveI : Nontrivial (Rings.Base (cycloOf P)) := hnon
    have hmonic : (modulusPoly P).Monic := modulusPoly_monic (P := P) hn
    refine
      (Polynomial.modByMonic_eq_self_iff (p := polyAsPolynomial P v) (q := modulusPoly P) hmonic).2 ?_
    have hn' : 0 < P.n := Nat.pos_of_ne_zero hn
    have hdegM : Polynomial.degree (modulusPoly P) = P.n := by
      simpa [modulusPoly, Rings.modulusPoly, cycloOf] using
        (Polynomial.degree_X_pow_add_C (R := Rings.Base (cycloOf P)) (n := P.n) hn'
          (a := (1 : Rings.Base (cycloOf P))))
    have hdegP : Polynomial.degree (polyAsPolynomial P v) < P.n := polyAsPolynomial_degree_lt (P := P) v
    simpa [hdegM] using hdegP

private theorem mod_out_eq_poly (P : MLWEParams) (hn : P.n ≠ 0) (v : Poly P.n P.q) :
    (Quotient.out (polyToRq P v)) %ₘ modulusPoly P = polyAsPolynomial P v := by
  classical
  let p := Quotient.out (polyToRq P v)
  let f := polyAsPolynomial P v
  have hq :
      (Ideal.Quotient.mk (Rings.cycloIdeal (cycloOf P))) p =
        (Ideal.Quotient.mk (Rings.cycloIdeal (cycloOf P))) f := by
    simp [p, f, polyToRq, Rings.mkRq]
  have hmem : p - f ∈ Rings.cycloIdeal (cycloOf P) := by
    have := (Ideal.Quotient.eq (I := Rings.cycloIdeal (cycloOf P)) (x := p) (y := f)).1 hq
    simpa using this
  have hdiv : modulusPoly P ∣ p - f := by
    simpa [Rings.cycloIdeal, modulusPoly, Rings.modulusPoly, cycloOf] using
      (Ideal.mem_span_singleton.1 hmem)
  have hmonic : (modulusPoly P).Monic := modulusPoly_monic (P := P) hn
  have hmod : p %ₘ modulusPoly P = f %ₘ modulusPoly P :=
    Polynomial.modByMonic_eq_of_dvd_sub (p₁ := p) (p₂ := f) (q := modulusPoly P) hmonic hdiv
  simpa [p, f, polyAsPolynomial_modByMonic (P := P) hn v] using hmod

theorem rqCoeffs_polyToRq (P : MLWEParams) (v : Poly P.n P.q) :
    rqCoeffs P (polyToRq P v) = v := by
  classical
  cases P with
  | mk n q k =>
      cases n with
      | zero =>
          funext i
          exact Fin.elim0 i
      | succ n' =>
          have hn : Nat.succ n' ≠ 0 := by simp
          funext i
          have hmod :
              (Quotient.out (polyToRq ⟨Nat.succ n', q, k⟩ v)) %ₘ modulusPoly ⟨Nat.succ n', q, k⟩ =
                polyAsPolynomial ⟨Nat.succ n', q, k⟩ v :=
            mod_out_eq_poly (P := ⟨Nat.succ n', q, k⟩) hn v
          simp [rqCoeffs, polyCoeffs, normalize, hmod, coeff_polyAsPolynomial]

noncomputable def mapPub (P : MLWEParams) (inst : MLWEInstance P) : RMLWEInstance P :=
  { A := fun i j => polyToRq P (inst.A i j)
    b := fun i => polyToRq P (inst.b i) }

noncomputable def mapSecret (P : MLWEParams) (s : MLWESecret P) : RMLWESecret P :=
  { inst := mapPub P s.inst
    s := fun i => polyToRq P (s.s i)
    e := fun i => polyToRq P (s.e i) }

noncomputable def decode (P : MLWEParams) (pub : MLWEInstance P) (r : RMLWESecret P) : MLWESecret P :=
  { inst := pub
    s := fun i => rqCoeffs P (r.s i)
    e := fun i => rqCoeffs P (r.e i) }

/-- Concrete bridge: ring-shaped MLWE recovery ⇒ coefficient-vector MLWE recovery. -/
noncomputable def bridgeRMLWEtoMLWE (P : MLWEParams) :
    Reduction.BridgeData (RMLWEView P) (MLWEView P) where
  mapPub := mapPub P
  mapSecret := mapSecret P
  decode := fun pub r => decode P pub r
  mapInstances := by
    intro _s _hs
    simp [RMLWEView]
  encode_comm := by
    intro _s
    rfl
  decode_correct := by
    intro s _hs r hr
    subst hr
    cases s with
    | mk inst sVec eVec =>
        simp [MLWEView, decode, mapSecret, rqCoeffs_polyToRq]

end RingReductions

end Lattice
end Crypto
end HeytingLean
