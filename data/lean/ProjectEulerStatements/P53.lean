import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace ProjectEulerStatements.P53

/-- Count of binomial coefficients `C(n,r)` with `1 ≤ n ≤ 100` exceeding one million. -/
def naive : Nat :=
  let limit := 1000000
  (List.range 101).foldl (fun acc n =>
    if n = 0 then acc
    else
      acc + (List.range (n + 1)).foldl (fun acc2 r =>
        if decide (Nat.choose n r > limit) then acc2 + 1 else acc2) 0) 0

example : Nat.choose 5 3 = 10 := by
  native_decide

example : Nat.choose 23 10 = 1144066 := by
  native_decide

end ProjectEulerStatements.P53
