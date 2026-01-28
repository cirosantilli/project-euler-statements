import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P36

def isPalindromeBase (b n : Nat) : Bool :=
  let ds := Nat.digits b n
  ds = ds.reverse
def isDoublePalindrome (n : Nat) : Bool :=
  isPalindromeBase 10 n && isPalindromeBase 2 n

def sumDoublePalindromes (limit : Nat) : Nat :=
  ((Finset.range limit).filter (fun n => isDoublePalindrome n)).sum (fun n => n)

def naive (limit : Nat) : Nat :=
  sumDoublePalindromes limit

example : isDoublePalindrome 585 = true := by
  native_decide

end ProjectEulerStatements.P36
