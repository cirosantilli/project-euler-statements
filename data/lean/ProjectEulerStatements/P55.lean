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

/-- Iterate a function `k` times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate f k (f n)

/-- Palindrome check after `k` reverse-and-add steps. -/
def palAt (n k : Nat) : Bool :=
  isPalindrome (iterate reverseAdd k n)

/-- Whether `n` reaches a palindrome within `maxIters` steps. -/
def reachesPalindrome (n maxIters : Nat) : Bool :=
  (List.range maxIters).any (fun k => palAt n k)

/-- A number is Lychrel (under a `maxIters` rule) if it does not reach a palindrome. -/
def isLychrel (n maxIters : Nat) : Bool :=
  !(reachesPalindrome n maxIters)

/-- Count possibly-Lychrel numbers under 50 iterations below `n`. -/
def naive (n : Nat) : Nat :=
  (List.range n).filter (fun x => isLychrel x 50) |>.length

example : palAt 47 1 = true := by
  native_decide

example : palAt 349 3 = true := by
  native_decide

end ProjectEulerStatements.P55
