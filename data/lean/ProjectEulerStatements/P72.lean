import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P72

def countReduced (d : Nat) : Nat :=
  (List.range d).foldl (fun acc n =>
    if decide (n < d ∧ Nat.gcd n d = 1) then acc + 1 else acc) 0

def totalCount (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc d =>
    if d ≤ 1 then acc else acc + countReduced d) 0

def naive (limit : Nat) : Nat :=
  totalCount limit

example : totalCount 8 = 21 := by
  native_decide

end ProjectEulerStatements.P72
