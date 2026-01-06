import HeytingLean.Crypto.FHE.Params
import HeytingLean.Crypto.FHE.Ciphertext
import HeytingLean.Crypto.FHE.Boot

/-!
  Minimal V0 core operations used by the CLI and selftest.
-/

namespace HeytingLean.Crypto.FHE

structure Key where
  p : Nat
deriving Repr, DecidableEq

def keygen (_secBits : Nat) : Key := { p := defaultParams.p }

def enc (_k : Key) (pt : Bool) : Ciphertext :=
  { val := if pt then 1 else 0, noise := 0 }

def dec (_k : Key) (c : Ciphertext) : Bool :=
  let n : Nat := Int.natAbs c.val
  n % 2 == 1

def add := Ciphertext.add
def mul := Ciphertext.mul

def boot (_k : Key) (c : Ciphertext) : Ciphertext :=
  Boot defaultParams c

end HeytingLean.Crypto.FHE
