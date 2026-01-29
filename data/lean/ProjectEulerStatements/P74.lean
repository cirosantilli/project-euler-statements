import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic

namespace ProjectEulerStatements.P74

def nextTerm (n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + Nat.factorial d) 0

def chainLen (n fuel : Nat) : Nat :=
  let rec go (x fuel : Nat) (seen : List Nat) : Nat :=
    match fuel with
    | 0 => seen.length
    | fuel + 1 =>
        if seen.contains x then seen.length
        else go (nextTerm x) fuel (x :: seen)
  go n fuel []

def countChains (limit target fuel : Nat) : Nat :=
  (List.range limit).foldl (fun acc n =>
    if chainLen n fuel = target then acc + 1 else acc) 0

def naive (limit target fuel : Nat) : Nat :=
  countChains limit target fuel

example : chainLen 69 20 = 5 := by
  native_decide

example : chainLen 78 20 = 4 := by
  native_decide

example : chainLen 540 20 = 2 := by
  native_decide

end ProjectEulerStatements.P74
