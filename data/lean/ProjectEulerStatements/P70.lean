import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P70

def phi (n : Nat) : Nat :=
  ((Finset.Icc 1 n).filter (fun k => Nat.gcd k n = 1)).card

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

def isPermutation (a b : Nat) : Bool :=
  digitsSorted a = digitsSorted b

def better (a b : Nat) : Bool :=
  if phi a = 0 ∨ phi b = 0 then false else
    a * phi b < b * phi a

def bestN (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun best n =>
    if decide (n > 1) && isPermutation n (phi n) then
      if decide (best = 0) || better n best then n else best
    else best) 0

def naive (limit : Nat) : Nat :=
  bestN limit

example : phi 9 = 6 := by
  native_decide

example : isPermutation 87109 79180 = true := by
  native_decide

end ProjectEulerStatements.P70
