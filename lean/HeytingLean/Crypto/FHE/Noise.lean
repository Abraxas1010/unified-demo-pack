import HeytingLean.Crypto.FHE.Ciphertext

/-!
  Noise measure and simple bounds used for early compilation.
  These will be strengthened later without changing client code.
-/

namespace HeytingLean.Crypto.FHE

open scoped Classical

abbrev Noise := Nat

open HeytingLean.Crypto.FHE

structure NoiseModel where
  /-- conservative bound for noise of a ciphertext -/ noise : (Ciphertext) → Noise

namespace SimpleNoise

open HeytingLean.Crypto.FHE

def noise (c : Ciphertext) : Noise := c.noise

theorem add_le (c₁ c₂ : Ciphertext) : noise (Ciphertext.add c₁ c₂) ≤ noise c₁ + noise c₂ := by
  simp [noise, Ciphertext.add]

theorem mul_le (c₁ c₂ : Ciphertext) : noise (Ciphertext.mul c₁ c₂) ≤ noise c₁ + noise c₂ + 1 := by
  simp [noise, Ciphertext.mul, Nat.add_assoc]

end SimpleNoise

end HeytingLean.Crypto.FHE
