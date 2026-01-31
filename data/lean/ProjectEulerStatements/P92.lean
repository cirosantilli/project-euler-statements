import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P92

def nextTerm (n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + d * d) 0

def endsAt89 (n : Nat) : Bool :=
  let rec go (x : Nat) (steps : Nat) : Bool :=
    match steps with
    | 0 => false
    | steps + 1 =>
        if x = 1 then false
        else if x = 89 then true
        else go (nextTerm x) steps
  go n (n + 1)

def count89 (limit : Nat) : Nat :=
  (List.range limit).foldl (fun acc n => if endsAt89 n then acc + 1 else acc) 0

def naive (limit : Nat) : Nat :=
  count89 limit

example : endsAt89 44 = false := by
  native_decide

example : endsAt89 85 = true := by
  native_decide

end ProjectEulerStatements.P92
