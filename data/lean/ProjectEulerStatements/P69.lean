import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P69

def phi (n : Nat) : Nat :=
  ((Finset.Icc 1 n).filter (fun k => Nat.gcd k n = 1)).card

def better (a b : Nat) : Bool :=
  if phi a = 0 ∨ phi b = 0 then false else
    a * phi b > b * phi a

def bestN (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun best n =>
    if better n best then n else best) 1

def naive (limit : Nat) : Nat :=
  bestN limit

example : phi 9 = 6 := by
  native_decide

example : bestN 10 = 6 := by
  native_decide

end ProjectEulerStatements.P69
