import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P92

def nextTerm (n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + d * d) 0

def endsAt89 (n fuel : Nat) : Bool :=
  let rec go (x fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
        if x = 1 then false
        else if x = 89 then true
        else go (nextTerm x) fuel
  go n fuel

def count89 (limit fuel : Nat) : Nat :=
  (List.range limit).foldl (fun acc n => if endsAt89 n fuel then acc + 1 else acc) 0

def naive (limit fuel : Nat) : Nat :=
  count89 limit fuel

example : endsAt89 44 20 = false := by
  native_decide

example : endsAt89 85 20 = true := by
  native_decide

end ProjectEulerStatements.P92
