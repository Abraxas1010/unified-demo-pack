import HeytingLean.Crypto.FHE.Params
import HeytingLean.Crypto.FHE.Ciphertext
import HeytingLean.Crypto.FHE.DecEval

/-!
  Noise-refresh nucleus `J` and basic laws.
-/

namespace HeytingLean.Crypto.FHE

/-- Noise-refresh nucleus: preserves value, trims noise to `min noise B0`. -/
def J (P : Params) (c : Ciphertext) : Ciphertext :=
  { val := c.val, noise := Nat.min c.noise P.B0 }

@[simp] theorem J_idem (P : Params) (c : Ciphertext) : J P (J P c) = J P c := by
  simp [J, Nat.min_assoc]

theorem Dec_preserved_by_J (P : Params) (c : Ciphertext) :
  Dec P (J P c) = Dec P c := by
  -- `J` does not change `val`.
  simp [J, Dec]

theorem noise_J_fresh (P : Params) (c : Ciphertext) : (J P c).noise ≤ P.B0 := by
  -- `min noise B0 ≤ B0`
  simpa [J] using Nat.min_le_right c.noise P.B0

end HeytingLean.Crypto.FHE
