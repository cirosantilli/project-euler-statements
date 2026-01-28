import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P38

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse

def numDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).length

def concatNat (a b : Nat) : Nat :=
  a * (10 ^ numDigits b) + b
def concatProduct (n k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => concatNat acc (n * (i + 1))) 0

def allDigitsOneToNine (l : List Nat) : Bool :=
  l.foldl (fun acc d => acc && decide (1 ≤ d ∧ d ≤ 9)) true

def isPandigital1to9 (n : Nat) : Bool :=
  let ds := digitsBE n
  decide (ds.length = 9) && allDigitsOneToNine ds && decide (ds.eraseDups.length = 9)

def listMax (l : List Nat) : Nat :=
  l.foldl Nat.max 0

def maxPandigital (limit : Nat) : Nat :=
  let candidates :=
    (List.range (limit + 1)).foldr (fun n acc =>
      (List.range 9).foldr (fun k acc2 =>
        if k + 1 ≤ 1 then acc2
        else
          let v := concatProduct n (k + 1)
          if numDigits v = 9 && isPandigital1to9 v then v :: acc2 else acc2) acc) []
  listMax candidates

def naive (limit : Nat) : Nat :=
  maxPandigital limit

example : concatProduct 192 3 = 192384576 := by
  native_decide

example : concatProduct 9 5 = 918273645 := by
  native_decide

end ProjectEulerStatements.P38
