import ProjectEulerStatements.P80
import Mathlib.Data.List.Range

/-! Exact decimal prefixes use integer scaling or truncation of the integer part. -/
namespace ProjectEulerStatements.SquareRootDigits

theorem truncated_bounds (n scale : Nat) (positive : 0 < scale) :
    (Nat.sqrt n / scale * scale) ^ 2 ≤ n ∧
      n < ((Nat.sqrt n / scale + 1) * scale) ^ 2 := by
  have lower := Nat.div_mul_le_self (Nat.sqrt n) scale
  have upper := Nat.lt_mul_div_succ (Nat.sqrt n) positive
  constructor
  · exact (Nat.pow_le_pow_left lower 2).trans (Nat.sqrt_le' n)
  · have next : Nat.sqrt n + 1 ≤ (Nat.sqrt n / scale + 1) * scale := by
      simpa [Nat.mul_comm] using upper
    exact (Nat.lt_succ_sqrt' n).trans_le (Nat.pow_le_pow_left next 2)

theorem prefix_bounds (n digits : Nat) :
    if digits < P80.integerWidth n then
      (P80.sqrtPrefix n digits * 10 ^ (P80.integerWidth n - digits)) ^ 2 ≤ n ∧
        n < ((P80.sqrtPrefix n digits + 1) * 10 ^ (P80.integerWidth n - digits)) ^ 2
    else
      (P80.sqrtPrefix n digits) ^ 2 ≤ n * 10 ^ (2 * (digits - P80.integerWidth n)) ∧
        n * 10 ^ (2 * (digits - P80.integerWidth n)) < (P80.sqrtPrefix n digits + 1) ^ 2 := by
  split <;> rename_i branch
  · simpa only [P80.sqrtPrefix, branch, ↓reduceIte] using
      truncated_bounds n (10 ^ (P80.integerWidth n - digits)) (Nat.pow_pos (by decide))
  · simpa only [P80.sqrtPrefix, branch, ↓reduceIte] using
      And.intro (Nat.sqrt_le' (n * 10 ^ (2 * (digits - P80.integerWidth n))))
        (Nat.lt_succ_sqrt' (n * 10 ^ (2 * (digits - P80.integerWidth n))))

@[simp] theorem sqrtDigitsSum_zero (digits : Nat) : P80.sqrtDigitsSum 0 digits = 0 := by
  simp [P80.sqrtDigitsSum, P80.isSquare]

theorem skip_zero (limit digits : Nat) :
    P80.naive limit digits =
      (List.range' 1 limit).foldl (fun total n => total + P80.sqrtDigitsSum n digits) 0 := by
  simp [P80.naive, P80.totalSum, List.range_eq_range', List.range'_succ]

end ProjectEulerStatements.SquareRootDigits
