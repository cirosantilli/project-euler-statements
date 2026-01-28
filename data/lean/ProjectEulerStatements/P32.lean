import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P32

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse

def allDigitsOneToNine (l : List Nat) : Bool :=
  l.foldl (fun acc d => acc && decide (1 ≤ d ∧ d ≤ 9)) true

def isPandigital1to9 (l : List Nat) : Bool :=
  decide (l.length = 9) && allDigitsOneToNine l && decide (l.eraseDups.length = 9)

def pandigitalProduct (a b : Nat) : Bool :=
  isPandigital1to9 (digitsBE a ++ digitsBE b ++ digitsBE (a * b))

def sumPandigitalProducts (maxA maxB : Nat) : Nat :=
  let products :=
    (List.range (maxA + 1)).foldr (fun a acc =>
      (List.range (maxB + 1)).foldr (fun b acc2 =>
        if a = 0 ∨ b = 0 then acc2
        else if pandigitalProduct a b then (a * b) :: acc2 else acc2) acc) []
  (products.eraseDups).foldl (fun acc x => acc + x) 0

def naive (maxA maxB : Nat) : Nat :=
  sumPandigitalProducts maxA maxB

example : pandigitalProduct 39 186 = true := by
  native_decide

end ProjectEulerStatements.P32
