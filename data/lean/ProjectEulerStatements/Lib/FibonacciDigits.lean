import ProjectEulerStatements.P25
import ProjectEulerStatements.Lib.DecimalDigits

/-! The first Fibonacci index meeting a decimal-length threshold, with an explicit bound. -/
namespace ProjectEulerStatements.FibonacciDigits
open P25

/-- A least-index specification shared by the recursive and iterative Python searches. -/
noncomputable def first (digits : Nat) : Nat := Nat.find (exists_fib_digits digits)

theorem first_spec (digits : Nat) : digits ≤ numDigits (Nat.fib (first digits)) :=
  Nat.find_spec (exists_fib_digits digits)

theorem before_first (digits index : Nat) (before : index < first digits) :
    numDigits (Nat.fib index) < digits := by
  have missing := Nat.find_min (exists_fib_digits digits) before
  change ¬ digits ≤ numDigits (Nat.fib index) at missing
  omega

theorem first_le_bound (digits : Nat) : first digits ≤ fibBound digits :=
  Nat.find_min' (exists_fib_digits digits) (fibBound_spec digits)

private theorem scan_first (digits index fuel : Nat) (before : index ≤ first digits)
    (enough : first digits < index + fuel) : firstFibWithDigits.go digits index fuel = first digits := by
  induction fuel generalizing index with
  | zero => omega
  | succ fuel ih =>
      rw [firstFibWithDigits.go]
      by_cases reached : digits ≤ numDigits (Nat.fib index)
      · rw [if_pos reached]
        have after : first digits ≤ index := Nat.find_min' (exists_fib_digits digits) reached
        omega
      · rw [if_neg reached]
        have more : index < first digits := by
          have := first_spec digits
          by_cases same : index = first digits
          · subst index
            contradiction
          · omega
        exact ih (index + 1) (by omega) (by omega)

/-- The statement's finite search finds exactly the least qualifying index. -/
theorem naive_eq_first (digits : Nat) : P25.naive digits = first digits := by
  apply scan_first digits 0 (fibBound digits + 1) (by omega)
  have := first_le_bound digits
  omega

theorem first_positive (digits : Nat) (positive : 0 < digits) : 0 < first digits := by
  have qualifies := first_spec digits
  by_cases zero : first digits = 0
  · simp [zero, numDigits] at qualifies
    omega
  · omega

theorem first_one : first 1 = 1 := by
  apply (Nat.find_eq_iff (exists_fib_digits 1)).mpr
  constructor
  · decide
  · intro index before
    have zero : index = 0 := by omega
    subst index
    decide

/-- Positive Fibonacci numbers have the same length in the source's two decimal conversions. -/
theorem fib_string_length (index : Nat) (positive : 0 < index) :
    (toString (Nat.fib index : Int)).toList.length = numDigits (Nat.fib index) := by
  apply DecimalDigits.int_string_length
  exact Nat.fib_pos.mpr positive

end ProjectEulerStatements.FibonacciDigits
