import Mathlib.Data.Rat.Init
import Mathlib.Tactic
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace ZK

/-- Embed booleans into `ℚ` via `0/1`. -/
def boolToRat : Bool → ℚ
  | true => 1
  | false => 0

@[simp] lemma boolToRat_true : boolToRat true = 1 := rfl

@[simp] lemma boolToRat_false : boolToRat false = 0 := rfl

@[simp] lemma boolToRat_mul_self (b : Bool) :
    boolToRat b * boolToRat b = boolToRat b := by
  cases b <;> norm_num [boolToRat]

@[simp] lemma boolToRat_sq_sub (b : Bool) :
    boolToRat b * (boolToRat b - 1) = 0 := by
  cases b <;> norm_num [boolToRat]

@[simp] lemma boolToRat_and (x y : Bool) :
    boolToRat (x && y) = boolToRat x * boolToRat y := by
  cases x <;> cases y <;> norm_num [boolToRat]

lemma boolToRat_or (x y : Bool) :
    boolToRat (x || y) =
      boolToRat x + boolToRat y - boolToRat x * boolToRat y := by
  cases x <;> cases y <;> norm_num [boolToRat]

lemma boolToRat_imp (x y : Bool) :
    boolToRat ((! x) || y) =
      1 - boolToRat x + boolToRat x * boolToRat y := by
  cases x <;> cases y <;> norm_num [boolToRat]

@[simp] lemma boolToRat_not (x : Bool) :
    boolToRat (! x) = 1 - boolToRat x := by
  cases x <;> norm_num [boolToRat]

lemma lin_eval_or
  {ρ : Var → ℚ} {vx vy vmul vz : Var}
  (Hx : ρ vmul = ρ vx * ρ vy)
  (Hz : ρ vz = ρ vx + ρ vy - ρ vx * ρ vy) :
  (⟨0, [(vz, 1), (vmul, 1), (vx, -1), (vy, -1)]⟩ : LinComb).eval ρ = 0 := by
  classical
  have hFold :
      (⟨0, [(vz, 1), (vmul, 1), (vx, -1), (vy, -1)]⟩ : LinComb).eval ρ =
        ρ vz + ρ vmul - ρ vx - ρ vy := by
    simp [LinComb.eval, sub_eq_add_neg, add_comm, add_assoc,
      List.foldl_cons, List.foldl_nil]
  calc
    (⟨0, [(vz, 1), (vmul, 1), (vx, -1), (vy, -1)]⟩ : LinComb).eval ρ
        = ρ vz + ρ vmul - ρ vx - ρ vy := hFold
    _ = (ρ vx + ρ vy - ρ vx * ρ vy) + ρ vmul - ρ vx - ρ vy := by
          simp [Hz, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = ρ vmul - ρ vx * ρ vy := by
          ring
    _ = 0 := by simp [Hx]

lemma lin_eval_imp
  {ρ : Var → ℚ} {vx vy vmul vz : Var}
  (Hx : ρ vmul = ρ vx * ρ vy)
  (Hz : ρ vz = 1 - ρ vy + ρ vy * ρ vx) :
  (⟨-1, [(vz, 1), (vy, 1), (vmul, -1)]⟩ : LinComb).eval ρ = 0 := by
  classical
  calc
    (⟨-1, [(vz, 1), (vy, 1), (vmul, -1)]⟩ : LinComb).eval ρ
        = ρ vz + ρ vy - ρ vmul - 1 := by
            simp [LinComb.eval, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc,
              List.foldl_cons, List.foldl_nil]
    _ = (1 - ρ vy + ρ vy * ρ vx) + ρ vy - ρ vmul - 1 := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              congrArg (fun t => t + ρ vy - ρ vmul - 1) Hz
    _ = (1 - ρ vy + ρ vy * ρ vx) + ρ vy - ρ vx * ρ vy - 1 := by
            simp [Hx, mul_comm]
    _ = 0 := by
            ring

end ZK
end Crypto
end HeytingLean
