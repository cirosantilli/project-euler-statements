import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P95

def properDivSum (n : Nat) : Nat :=
  if n = 0 then 0 else
  ((Finset.Icc 1 (n - 1)).filter (fun d => d ∣ n)).sum (fun x => x)

def chain (start limit fuel : Nat) : List Nat :=
  let rec go (x fuel : Nat) (seen : List Nat) : List Nat :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
        if x = 0 ∨ x > limit then []
        else if seen.contains x then
          if x = start then seen.reverse else []
        else
          go (properDivSum x) fuel (x :: seen)
  go start fuel []

def longestChain (limit fuel : Nat) : List Nat :=
  (List.range (limit + 1)).foldl (fun best n =>
    let c := chain n limit fuel
    if c.length > best.length then c else best) []

def naive (limit fuel : Nat) : Nat :=
  let c := longestChain limit fuel
  match c with
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

example : properDivSum 28 = 28 := by
  native_decide

end ProjectEulerStatements.P95
