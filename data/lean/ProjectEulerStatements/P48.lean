import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P48

def modPow (a b m : Nat) : Nat :=
  let rec go (a b acc : Nat) : Nat :=
    match b with
    | 0 => acc
    | b + 1 => go a b (acc * a % m)
  go (a % m) b 1

def seriesMod (n m : Nat) : Nat :=
  (List.range n).foldl (fun acc i => (acc + modPow (i + 1) (i + 1) m) % m) 0

def naive (n : Nat) : Nat :=
  seriesMod n (10 ^ 10)

example : seriesMod 10 (10 ^ 10) = 10405071317 % (10 ^ 10) := by
  native_decide

end ProjectEulerStatements.P48
