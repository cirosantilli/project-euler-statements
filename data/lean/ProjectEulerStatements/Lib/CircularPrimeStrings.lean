import ProjectEulerStatements.Lib.CircularPrimeOrbits
import ProjectEulerStatements.Lib.DecimalDigits
import Mathlib.Data.Nat.Digits.Lemmas

namespace ProjectEulerStatements.CircularPrimes

set_option Elab.async false

theorem naive_small (limit : Nat) (small : limit ≤ 2) : P35.naive limit = 0 := by
  have alternatives : limit = 0 ∨ limit = 1 ∨ limit = 2 := by omega
  rcases alternatives with rfl | rfl | rfl <;> decide +kernel

theorem decimal_characters (n : Nat) (positive : 0 < n) :
    (toString (n : Int)).toList = (P35.digitsBE n).map Nat.digitChar := by
  simpa [toString, Int.repr, Nat.repr, P35.digitsBE] using
    DecimalDigits.toDigits_eq_digitChars n positive

def allowedCharacter (character : Char) : Bool :=
  (['1', '3', '7', '9'] : List Char).contains character

theorem allowedCharacter_digit (digit : Nat) (bound : digit < 10) :
    allowedCharacter (Nat.digitChar digit) =
      decide (digit = 1 ∨ digit = 3 ∨ digit = 7 ∨ digit = 9) := by
  interval_cases digit <;> decide

theorem allowed_string_iff (n : Nat) (positive : 0 < n) :
    (toString (n : Int)).toList.all allowedCharacter = true ↔ AllowedDigits (P35.digitsBE n) := by
  rw [decimal_characters n positive]
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, AllowedDigits]
  constructor
  · intro allowed digit member
    simpa only [allowedCharacter_digit digit (digitsBE_bounds n digit member),
      decide_eq_true_eq] using
      allowed digit member
  · intro allowed digit member
    simpa only [allowedCharacter_digit digit (digitsBE_bounds n digit member),
      decide_eq_true_eq] using
      allowed digit member

theorem rotation_lt_sieve (limit n rotation : Nat) (inside : n < limit)
    (member : rotation ∈ rotationValues n) :
    rotation < 10 ^ (P35.digitsBE (limit - 1)).length := by
  have widths : (P35.digitsBE n).length ≤ (P35.digitsBE (limit - 1)).length := by
    simpa [P35.digitsBE] using Nat.le_length_digits_le 10 n (limit - 1) (by omega)
  exact Nat.lt_of_lt_of_le (rotationValues_bound n rotation member)
    (Nat.pow_le_pow_right (by decide) widths)

theorem digitsBE_length_ge_two (n : Nat) : 2 ≤ (P35.digitsBE n).length ↔ 10 ≤ n := by
  have small := Nat.digits_length_le_iff (b := 10) (k := 1) (by decide) n
  simp only [P35.digitsBE, List.length_reverse]
  norm_num at small
  omega

end ProjectEulerStatements.CircularPrimes
