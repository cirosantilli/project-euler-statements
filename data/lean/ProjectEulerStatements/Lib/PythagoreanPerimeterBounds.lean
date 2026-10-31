import ProjectEulerStatements.Lib.PythagoreanPerimeterCountingProof
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Bitwise

/-! Square-root truncation and an increasing-perimeter break preserve the complete table. -/
namespace ProjectEulerStatements.PythagoreanPerimeterCounting
set_option Elab.async false

def maxParameter (limit : Nat) : Nat := Nat.sqrt (limit / 2) + 1

theorem xor_parity (m n : Nat) (ordered : n ≤ m) :
    (m ^^^ n) &&& 1 = (m - n) % 2 := by
  rw [Nat.and_one_is_mod, Nat.xor_mod_two_eq]
  omega

theorem row_append (limit m first left right : Nat) (counts : Table) :
    row limit m first (left + right) counts =
      row limit m (first + left) right (row limit m first left counts) := by
  simp only [row, ← List.range'_append_1, List.foldl_append]

theorem row_inactive (limit m first count : Nat) (counts : Table)
    (stopped : limit < perimeter m first) : row limit m first count counts = counts := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      rw [row_step]
      have rejected : permitted limit m first = false := by simp [permitted, not_le.mpr stopped]
      simp only [rejected, Bool.false_eq_true, if_false]
      apply ih
      have grows : perimeter m first ≤ perimeter m (first + 1) := by
        unfold perimeter
        exact Nat.mul_le_mul_left _ (by omega)
      omega

theorem outer_append (limit first left right : Nat) (counts : Table) :
    outer limit first (left + right) counts =
      outer limit (first + left) right (outer limit first left counts) := by
  simp only [outer, ← List.range'_append_1, List.foldl_append]

theorem parameter_count_le (limit : Nat) : Nat.sqrt (limit / 2) ≤ limit - 1 := by
  have bounded := Nat.sqrt_le_self (limit / 2)
  omega

theorem after_max_inactive (limit : Nat) :
    limit < 2 * (maxParameter limit + 1) * (maxParameter limit + 1 + 1) := by
  have square := Nat.lt_succ_sqrt (limit / 2)
  have division : limit < 2 * (limit / 2 + 1) := by omega
  dsimp only [maxParameter]
  nlinarith

/-- Every omitted outer parameter has even its smallest positive perimeter above the bound. -/
theorem table_at_sqrt (limit : Nat) :
    outer limit 2 (Nat.sqrt (limit / 2)) (fun _ => 0) = table limit := by
  have count := parameter_count_le limit
  have split : limit - 1 = Nat.sqrt (limit / 2) + (limit - 1 - Nat.sqrt (limit / 2)) := by omega
  unfold table
  rw [split, outer_append]
  have stopped : limit < 2 * (2 + Nat.sqrt (limit / 2)) * (2 + Nat.sqrt (limit / 2) + 1) := by
    have same : 2 + Nat.sqrt (limit / 2) = maxParameter limit + 1 := by
      dsimp only [maxParameter]
      omega
    rw [same]
    exact after_max_inactive limit
  exact (outer_inactive _ _ _ _ stopped).symm

end ProjectEulerStatements.PythagoreanPerimeterCounting
