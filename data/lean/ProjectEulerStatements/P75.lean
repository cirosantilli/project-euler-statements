import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P75

def countSolutions (p : Nat) : Nat :=
  (List.range (p + 1)).foldl (fun acc a =>
    (List.range (p + 1)).foldl (fun acc2 b =>
      let c := p - a - b
      if a < b ∧ b < c ∧ a^2 + b^2 = c^2 then acc2 + 1 else acc2) acc) 0

def countSingular (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc p =>
    if countSolutions p = 1 then acc + 1 else acc) 0

def naive (limit : Nat) : Nat :=
  countSingular limit

example : countSolutions 12 = 1 := by
  native_decide

example : countSolutions 120 = 3 := by
  native_decide

end ProjectEulerStatements.P75
