/-!
  Ciphertext carrier and basic operations (scaffold).
  The semantics in V0 are intentionally lightweight and can be refined.
-/

namespace HeytingLean.Crypto.FHE

structure Ciphertext where
  val   : Int
  noise : Nat := 0
deriving Repr, DecidableEq

namespace Ciphertext

def add (c₁ c₂ : Ciphertext) : Ciphertext :=
  { val := c₁.val + c₂.val, noise := c₁.noise + c₂.noise }

def mul (c₁ c₂ : Ciphertext) : Ciphertext :=
  { val := c₁.val * c₂.val, noise := c₁.noise + c₂.noise + 1 }

end Ciphertext

end HeytingLean.Crypto.FHE
