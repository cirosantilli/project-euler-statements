import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P95

def properDivSum (n : Nat) : Nat :=
  if n = 0 then 0 else
  ((Finset.Icc 1 (n - 1)).filter (fun d => d ∣ n)).sum (fun x => x)

def chain (start limit : Nat) : List Nat :=
  let rec go (x : Nat) (seen : List Nat) (steps : Nat) : List Nat :=
    match steps with
    | 0 => []
    | steps + 1 =>
        if x = 0 ∨ x > limit then []
        else if seen.contains x then
          if x = start then seen.reverse else []
        else
          go (properDivSum x) (x :: seen) steps
  go start [] (limit + 1)

def longestChain (limit : Nat) : List Nat :=
  (List.range (limit + 1)).foldl (fun best n =>
    let c := chain n limit
    if c.length > best.length then c else best) []

def naive (limit : Nat) : Nat :=
  let c := longestChain limit
  match c with
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

example : properDivSum 28 = 28 := by
  native_decide

end ProjectEulerStatements.P95
