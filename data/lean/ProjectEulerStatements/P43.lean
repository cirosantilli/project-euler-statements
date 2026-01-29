import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P43

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse

def digitsToNat (l : List Nat) : Nat :=
  Nat.ofDigits 10 l.reverse

def subNum (l : List Nat) (i : Nat) : Nat :=
  digitsToNat ((l.drop i).take 3)

def hasProperty (l : List Nat) : Bool :=
  decide (l.length = 10) &&
    decide (l.eraseDups.length = 10) &&
    decide (subNum l 1 % 2 = 0) &&
    decide (subNum l 2 % 3 = 0) &&
    decide (subNum l 3 % 5 = 0) &&
    decide (subNum l 4 % 7 = 0) &&
    decide (subNum l 5 % 11 = 0) &&
    decide (subNum l 6 % 13 = 0) &&
    decide (subNum l 7 % 17 = 0)

def pandigitalNums : List Nat :=
  let digits := (List.range 10)
  let perms := digits.permutations
  perms.map digitsToNat

def sumWithProperty : Nat :=
  (pandigitalNums.filter (fun n => hasProperty (digitsBE n))).foldl (fun acc n => acc + n) 0

def naive : Nat :=
  sumWithProperty

example : hasProperty (digitsBE 1406357289) = true := by
  native_decide

end ProjectEulerStatements.P43
