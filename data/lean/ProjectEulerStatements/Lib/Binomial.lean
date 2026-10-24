import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! Exact multiplicative computation of binomial coefficients. -/
namespace ProjectEulerStatements.Binomial

/-- One factor advances both the upper and lower binomial indices. -/
theorem multiplicative_step (offset k : Nat) :
    Nat.choose (offset + k) k * (offset + k + 1) / (k + 1) =
      Nat.choose (offset + (k + 1)) (k + 1) := by
  rw [Nat.mul_comm, Nat.add_one_mul_choose_eq, Nat.mul_div_cancel]
  · simp [Nat.add_assoc]
  · omega

/-- Any implementation of the exact recurrence computes the binomial coefficient. -/
theorem recurrence_eq (offset : Nat) (f : Nat → Nat) (zero : f 0 = 1)
    (step : ∀ k, f (k + 1) = f k * (offset + k + 1) / (k + 1)) (k : Nat) :
    f k = Nat.choose (offset + k) k := by
  induction k with
  | zero => simpa using zero
  | succ k ih => rw [step, ih, multiplicative_step]

/-- Complementing the lower index preserves the coefficient. -/
theorem choose_min (n k : Nat) (bound : k ≤ n) :
    Nat.choose n (min k (n - k)) = Nat.choose n k := by
  by_cases small : k ≤ n - k
  · rw [Nat.min_eq_left small]
  · rw [Nat.min_eq_right (by omega), Nat.choose_symm bound]

end ProjectEulerStatements.Binomial
