import HeytingLean.Crypto.Lattice.RecoveryViews

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# First concrete reduction step (v0.7)

This file adds a *reviewable* (but still statement-first) reduction connecting the concrete carriers
introduced in `Problems.lean`:

`MLWE` ⇒ `LWE` via “take coefficient 0” (and embed LWE instances as constant polynomials).

This is not a cryptographic claim about MLWE/LWE distributions; it is a precise statement about the
relationship between the *recovery views* (`RecoveryView`) once a concrete embedding/projection is
fixed.
-/

namespace MLWEToLWE

/-- Extract an `LWEParams` from an `MLWEParams` by keeping only the module rank `k`
(as both rows and columns) and modulus `q`. -/
def lweParamsOf (P : MLWEParams) : LWEParams :=
  { n := P.k, m := P.k, q := P.q }

variable {P : MLWEParams} (hn : 0 < P.n)

private def fin0 : Fin P.n := ⟨0, hn⟩

/-- Embed a scalar as a coefficient-vector of length `n` by placing it at coefficient `0`. -/
def polyConst (a : Zq P.q) : Poly P.n P.q :=
  fun i => if i = fin0 (P := P) hn then a else 0

/-- Extract coefficient `0` from a coefficient-vector. -/
def coeff0 (p : Poly P.n P.q) : Zq P.q :=
  p (fin0 (P := P) hn)

@[simp] theorem coeff0_polyConst (a : Zq P.q) :
    coeff0 (P := P) hn (polyConst (P := P) hn a) = a := by
  simp [coeff0, polyConst, fin0]

/-- Embed an LWE public instance as an MLWE public instance by using constant polynomials. -/
def embedLWEInstance (inst : LWEInstance (lweParamsOf P)) : MLWEInstance P :=
  { A := fun i j => polyConst (P := P) hn (inst.A i j)
    b := fun i => polyConst (P := P) hn (inst.b i) }

/-- Embed an LWE secret as an MLWE secret by using constant polynomials. -/
def embedLWESecret (s : LWESecret (lweParamsOf P)) : MLWESecret P :=
  { inst := embedLWEInstance (P := P) hn s.inst
    s := fun i => polyConst (P := P) hn (s.s i)
    e := fun i => polyConst (P := P) hn (s.e i) }

/-- Project an MLWE secret back to an LWE secret by taking coefficient `0`. -/
def projectMLWESecret (pub : LWEInstance (lweParamsOf P)) (s : MLWESecret P) :
    LWESecret (lweParamsOf P) :=
  { inst := pub
    s := fun i => coeff0 (P := P) hn (s.s i)
    e := fun i => coeff0 (P := P) hn (s.e i) }

/-- Concrete reduction: if one can recover `MLWESecret`, then one can recover the embedded
coefficient-`0` `LWESecret`. -/
def reduction : Reduction (MLWEView P) (LWEView (lweParamsOf P)) where
  mapPub := embedLWEInstance (P := P) hn
  mapSecret := embedLWESecret (P := P) hn
  lift := fun recoverMLWE pub =>
    projectMLWESecret (P := P) hn pub (recoverMLWE (embedLWEInstance (P := P) hn pub))
  sound := by
    intro recoverMLWE hsolve
    intro sLWE
    -- Use correctness of `recoverMLWE` on the embedded secret.
    have hrec :
        recoverMLWE (embedLWEInstance (P := P) hn sLWE.inst) =
          embedLWESecret (P := P) hn sLWE := by
      have h := hsolve (embedLWESecret (P := P) hn sLWE)
      have h' := h (by simp [MLWEView])
      simpa [MLWEView, RecoveryView.succeedsOn, embedLWESecret, embedLWEInstance] using h'
    -- Now coefficient-0 projection inverts the embedding, componentwise.
    cases sLWE with
    | mk inst s e =>
      intro _
      -- Unfold the goal for `LWEView` and rewrite via correctness on the embedded secret.
      simp [LWEView]
      rw [hrec]
      simp [projectMLWESecret, embedLWESecret, embedLWEInstance, coeff0, polyConst, fin0]

end MLWEToLWE

end Lattice
end Crypto
end HeytingLean
