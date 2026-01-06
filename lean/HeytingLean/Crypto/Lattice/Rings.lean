import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Cyclotomic-style ring scaffolding for Kyber-style parameters

This module upgrades the previous placeholder carrier to an actual polynomial quotient ring:

`R_q = (ZMod q)[X] ⧸ ⟨X^n + 1⟩`

This is a **carrier-level** model intended for stating lattice problems over the standard Kyber
ring shape; it does not attempt to model NTT representations or sampling in this file.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice

structure CycloParams where
  n : Nat := 256
  q : Nat := 3329
  deriving Repr, DecidableEq

namespace Rings

def modulus (p : CycloParams) : Nat := p.q

open scoped Polynomial

abbrev Base (p : CycloParams) : Type := ZMod p.q

abbrev Poly (p : CycloParams) : Type := Polynomial (Base p)

/-- The Kyber-style modulus polynomial `X^n + 1`. -/
noncomputable def modulusPoly (p : CycloParams) : Poly p :=
  Polynomial.X ^ p.n + 1

/-- The principal ideal `⟨X^n + 1⟩` in `(ZMod q)[X]`. -/
noncomputable def cycloIdeal (p : CycloParams) : Ideal (Poly p) :=
  Ideal.span ({ modulusPoly p } : Set (Poly p))

/-- Cyclotomic-style quotient ring `R_q = (ZMod q)[X] / ⟨X^n + 1⟩`. -/
abbrev Rq (p : CycloParams) : Type :=
  Poly p ⧸ cycloIdeal p

noncomputable def mkRq (p : CycloParams) : Poly p →+* Rq p :=
  Ideal.Quotient.mk (cycloIdeal p)

end Rings
end Lattice
end Crypto
end HeytingLean
