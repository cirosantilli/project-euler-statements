import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P4

def isPalindrome (n : Nat) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

instance : DecidablePred isPalindrome := by
  intro n
  unfold isPalindrome
  infer_instance

def digitLower (digits : Nat) : Nat :=
  match digits with
  | 0 => 0
  | d + 1 => 10 ^ d

def digitUpper (digits : Nat) : Nat :=
  10 ^ digits - 1

def palProductSet (digits : Nat) : Finset Nat :=
  let lo := digitLower digits
  let hi := digitUpper digits
  (((Finset.Icc lo hi).product (Finset.Icc lo hi)).image (fun p => p.1 * p.2)).filter
    (fun n => isPalindrome n)

/-- Largest palindrome made from the product of two numbers with `digits` decimal digits. -/
def naive (digits : Nat) : Nat :=
  let s := palProductSet digits
  if h : s.Nonempty then s.max' h else 0

example : naive 2 = 9009 := by
  native_decide

end ProjectEulerStatements.P4
