import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic

namespace ProjectEulerStatements.P74

def nextTerm (n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + Nat.factorial d) 0

def chainLen (n : Nat) : Nat :=
  let rec go (x : Nat) (seen : List Nat) (steps : Nat) : Nat :=
    match steps with
    | 0 => seen.length
    | steps + 1 =>
        if seen.contains x then seen.length
        else go (nextTerm x) (x :: seen) steps
  go n [] (n + 1)

def countChains (limit target : Nat) : Nat :=
  (List.range limit).foldl (fun acc n =>
    if chainLen n = target then acc + 1 else acc) 0

def naive (limit target : Nat) : Nat :=
  countChains limit target

example : chainLen 69 = 5 := by
  native_decide

example : chainLen 78 = 4 := by
  native_decide

example : chainLen 540 = 2 := by
  native_decide

end ProjectEulerStatements.P74
