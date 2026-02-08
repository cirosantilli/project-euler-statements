import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P55

/-- Reverse digits of a natural number. -/
def reverseDigits (n : Nat) : Nat :=
  Nat.ofDigits 10 (Nat.digits 10 n |>.reverse)

/-- Check if a number is palindromic in base 10. -/
def isPalindrome (n : Nat) : Bool :=
  let ds := Nat.digits 10 n
  ds = ds.reverse

/-- One reverse-and-add step. -/
def reverseAdd (n : Nat) : Nat :=
  n + reverseDigits n

/-- Whether `n` becomes palindromic within `fuel` steps. -/
def reachesPalindrome (n fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      let m := reverseAdd n
      if isPalindrome m then true else reachesPalindrome m fuel

/-- A number is Lychrel (under the 50-iteration rule) if it does not reach a palindrome. -/
def isLychrel (n : Nat) : Bool :=
  !(reachesPalindrome n 50)

/-- Count Lychrel numbers below ten-thousand. -/
def naive : Nat :=
  (List.range 10000).filter isLychrel |>.length

example : reachesPalindrome 47 1 = true := by
  native_decide

example : reachesPalindrome 349 3 = true := by
  native_decide

end ProjectEulerStatements.P55
