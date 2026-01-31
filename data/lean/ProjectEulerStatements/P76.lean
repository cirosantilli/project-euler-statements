import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P76

def countWays (n max : Nat) : Nat :=
  let rec go (n max : Nat) : Nat :=
    if n = 0 then 1
    else if max = 0 then 0
    else
      let withMax := if max ≤ n then go (n - max) max else 0
      let withoutMax := go n (max - 1)
      withMax + withoutMax
  termination_by n + max
  decreasing_by
    all_goals
      omega
  go n max

def naive (n : Nat) : Nat :=
  countWays n (n - 1)

example : naive 5 = 6 := by
  native_decide

end ProjectEulerStatements.P76
