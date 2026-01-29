import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P76

def countWays (n max : Nat) : Nat :=
  let rec go (n max fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if n = 0 then 1
        else if max = 0 then 0
        else
          let withMax := if max ≤ n then go (n - max) max fuel else 0
          let withoutMax := go n (max - 1) fuel
          withMax + withoutMax
  go n max (n + max + 1)

def naive (n : Nat) : Nat :=
  countWays n (n - 1)

example : naive 5 = 6 := by
  native_decide

end ProjectEulerStatements.P76
