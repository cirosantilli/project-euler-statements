import ProjectEulerStatements.P12
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Splitting a triangular number into coprime factors before counting divisors. -/
namespace ProjectEulerStatements.P12

def splitLeft (n : Nat) : Nat := if n % 2 = 0 then n / 2 else n

def splitRight (n : Nat) : Nat := if n % 2 = 0 then n + 1 else (n + 1) / 2

theorem triangle_eq_split (n : Nat) : triangle n = splitLeft n * splitRight n := by
  by_cases even : n % 2 = 0
  · have divides : 2 ∣ n := Nat.dvd_of_mod_eq_zero even
    simpa [triangle, splitLeft, splitRight, even, Nat.mul_comm] using
      Nat.mul_div_assoc (n + 1) divides
  · have divides : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    simpa [triangle, splitLeft, splitRight, even] using Nat.mul_div_assoc n divides

theorem split_coprime (n : Nat) : (splitLeft n).Coprime (splitRight n) := by
  have consecutive : n.Coprime (n + 1) := by simp
  by_cases even : n % 2 = 0
  · have divides : 2 ∣ n := Nat.dvd_of_mod_eq_zero even
    simpa [splitLeft, splitRight, even] using
      consecutive.of_dvd_left (Nat.div_dvd_of_dvd divides)
  · have divides : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    simpa [splitLeft, splitRight, even] using
      consecutive.of_dvd_right (Nat.div_dvd_of_dvd divides)

theorem split_positive (n : Nat) (positive : 0 < n) : 0 < splitLeft n ∧ 0 < splitRight n := by
  by_cases even : n % 2 = 0
  · simp only [splitLeft, splitRight, if_pos even]
    omega
  · simp only [splitLeft, splitRight, if_neg even]
    omega

/-- Divisor counts multiply because the optimized split has coprime factors. -/
theorem divisorCount_triangle_split (n : Nat) :
    divisorCount (triangle n) = divisorCount (splitLeft n) * divisorCount (splitRight n) := by
  rw [triangle_eq_split]
  exact (split_coprime n).card_divisors_mul

end ProjectEulerStatements.P12
