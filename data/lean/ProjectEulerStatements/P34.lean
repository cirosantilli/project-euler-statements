import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic

namespace ProjectEulerStatements.P34

def digitFactSum (n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + Nat.factorial d) 0

def sumCurious (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl
    (fun acc n =>
      if n = 1 ∨ n = 2 then acc
      else if digitFactSum n = n then acc + n else acc)
    0
def naive (limit : Nat) : Nat :=
  sumCurious limit

example : digitFactSum 145 = 145 := by
  native_decide

end ProjectEulerStatements.P34
