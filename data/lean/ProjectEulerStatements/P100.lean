import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P100

def next (b t : Nat) : Nat × Nat :=
  (3 * b + 2 * t - 2, 4 * b + 3 * t - 3)

def firstOver (limit : Nat) : Nat :=
  let rec go (b t steps : Nat) : Nat :=
    match steps with
    | 0 => 0
    | steps + 1 =>
        if t > limit then b
        else
          let p := next b t
          go p.1 p.2 steps
  go 15 21 (limit + 1)

def naive (limit : Nat) : Nat :=
  firstOver limit

example : 2 * 15 * 14 = 21 * 20 := by
  native_decide

example : 2 * 85 * 84 = 120 * 119 := by
  native_decide

end ProjectEulerStatements.P100
