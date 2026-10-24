import Mathlib.Data.Nat.Factorial.Basic

/-! Characterization of factorial by its defining recurrence. -/
namespace ProjectEulerStatements.Factorial

theorem recurrence_eq (f : Nat → Nat) (zero : f 0 = 1)
    (successor : ∀ n, f (n + 1) = (n + 1) * f n) (n : Nat) :
    f n = Nat.factorial n := by
  induction n with
  | zero => exact zero
  | succ n ih => rw [successor, ih, Nat.factorial_succ]

end ProjectEulerStatements.Factorial
