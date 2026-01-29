import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P73

def countBetween (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc d =>
    (List.range d).foldl (fun acc2 n =>
      if decide (n < d ∧ Nat.gcd n d = 1 ∧ n * 2 < d ∧ n * 3 > d) then acc2 + 1 else acc2) acc) 0

def naive (limit : Nat) : Nat :=
  countBetween limit

example : countBetween 8 = 3 := by
  native_decide

end ProjectEulerStatements.P73
