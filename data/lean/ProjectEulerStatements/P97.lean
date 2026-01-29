import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P97

def modPow (a b m : Nat) : Nat :=
  let rec go (a b acc : Nat) : Nat :=
    match b with
    | 0 => acc
    | b + 1 => go a b (acc * a % m)
  go (a % m) b 1

def naive : Nat :=
  let m := 10 ^ 10
  (28433 * modPow 2 7830457 m + 1) % m

end ProjectEulerStatements.P97
