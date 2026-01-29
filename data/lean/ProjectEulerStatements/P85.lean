import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P85

def rectCount (m n : Nat) : Nat :=
  (m * (m + 1) / 2) * (n * (n + 1) / 2)

def nearestArea (target limit : Nat) : Nat :=
  let rec go (m n bestArea bestDiff : Nat) : Nat :=
    if m = 0 then bestArea else
      let count := rectCount m n
      let diff := if count ≥ target then count - target else target - count
      let (bestArea', bestDiff') := if diff < bestDiff then (m * n, diff) else (bestArea, bestDiff)
      if n = 0 then go (m - 1) limit bestArea' bestDiff' else go m (n - 1) bestArea' bestDiff'
  go limit limit 0 target

def naive (target limit : Nat) : Nat :=
  nearestArea target limit

example : rectCount 3 2 = 18 := by
  native_decide

end ProjectEulerStatements.P85
