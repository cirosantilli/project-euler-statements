import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax

namespace ProjectEulerStatements.P39

def countSolutions (p : Nat) : Nat :=
  (List.range (p + 1)).foldl (fun acc a =>
    (List.range (p + 1)).foldl (fun acc2 b =>
      let c := p - a - b
      if a < b ∧ b < c ∧ a^2 + b^2 = c^2 then acc2 + 1 else acc2) acc) 0

def maxPerimeter (limit : Nat) : Nat :=
  match List.argmax (fun p => countSolutions p) (List.range (limit + 1)) with
  | some p => p
  | none => 0
def naive (limit : Nat) : Nat :=
  maxPerimeter limit

example : countSolutions 120 = 3 := by
  native_decide

end ProjectEulerStatements.P39
