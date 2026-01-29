import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P78

def partition (n : Nat) : Nat :=
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
  go n n (n + n + 1)

def firstDivisible (limit : Nat) : Nat :=
  match (List.find? (fun n => partition n % 1000000 = 0) (List.range (limit + 1))) with
  | some n => n
  | none => 0

def naive (limit : Nat) : Nat :=
  firstDivisible limit

example : partition 5 = 7 := by
  native_decide

end ProjectEulerStatements.P78
