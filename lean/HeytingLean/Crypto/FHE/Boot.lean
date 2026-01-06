import HeytingLean.Crypto.FHE.Nucleus
import HeytingLean.Crypto.FHE.DecEval

/-!
  Bootstrapping operator scaffold.
-/

namespace HeytingLean.Crypto.FHE

open HeytingLean.Crypto.FHE

def Boot (P : Params) (c : Ciphertext) : Ciphertext :=
  J P (evalHomDec P c)

@[simp] theorem Boot_idem (P : Params) (c : Ciphertext) : Boot P (Boot P c) = Boot P c := by
  -- with identity `J` and `evalHomDec = id`
  simp [Boot, J, evalHomDec]

/-- Bootstrapping preserves decryption in the V0 scaffold. -/
theorem Dec_preserved_by_Boot (P : Params) (c : Ciphertext) :
  Dec P (Boot P c) = Dec P c := by
  -- In V0, `Boot` reduces to `J` and `Dec` ignores the noise field.
  -- We reuse the nucleus-level preservation lemma.
  have := HeytingLean.Crypto.FHE.Dec_preserved_by_J P c
  -- `Boot P c = J P c` because `evalHomDec` is the identity.
  simpa [Boot, evalHomDec] using this

/-- Bootstrapping refreshes the noise budget down to the post-refresh bound. -/
theorem noise_Boot_fresh (P : Params) (c : Ciphertext) :
  (Boot P c).noise ≤ P.B0 := by
  -- `Boot` is just `J` after an identity homomorphic decryption.
  simpa [Boot, evalHomDec] using HeytingLean.Crypto.FHE.noise_J_fresh P c

/-- Under sane parameters, a single bootstrapping step yields noise strictly
below the configured threshold `T`. -/
theorem noise_Boot_lt_T {P : Params} (h : Params.sane P) (c : Ciphertext) :
  (Boot P c).noise < P.T := by
  rcases h with ⟨_, hB0_lt_T, _⟩
  have hnoise : (Boot P c).noise ≤ P.B0 := noise_Boot_fresh P c
  exact Nat.lt_of_le_of_lt hnoise hB0_lt_T

end HeytingLean.Crypto.FHE
