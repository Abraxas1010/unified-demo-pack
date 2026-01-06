import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.BoolLens

namespace HeytingLean
namespace Crypto
namespace ZK
namespace IR

/--
Lightweight interface that any ZK backend can implement. It is intentionally
generic and compiled from the existing BoolLens VM in this codebase.
-/
structure Backend (F : Type) where
  Sys      : Type
  Assign   : Type
  compile  : ∀ {n}, BoolLens.Env n → Program n → Sys
  satisfies : Sys → Assign → Prop
  publicOut : Sys → Assign → List F

/--
Backend law schema. Concrete backends can specialise this to state
soundness/completeness w.r.t. the BoolLens canonical run.  We keep this as a
container of \emph{statements}, without providing proofs here, so that
individual backends can give precise formulations elsewhere.
-/
structure Laws {F : Type} (B : Backend F) : Type where
  sound : Prop
  complete : Prop

end IR
end ZK
end Crypto
end HeytingLean
