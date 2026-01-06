import HeytingLean.Crypto.FHE.Ciphertext

/-!
  Decryption circuit model and homomorphic evaluation (V0).
-/

namespace HeytingLean.Crypto.FHE

open HeytingLean.Crypto.FHE

/-- parity-based decryption for V0: true iff `val` is odd -/
def Dec (_P : Params) (c : Ciphertext) : Bool :=
  let v : Int := c.val
  let n : Nat := Int.natAbs v
  n % 2 == 1

/-- homomorphic evaluation of the decryption circuit (V0: identity) -/
def evalHomDec (_P : Params) (c : Ciphertext) : Ciphertext := c

end HeytingLean.Crypto.FHE
