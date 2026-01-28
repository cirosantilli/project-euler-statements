import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P29

def powers (aMax bMax : Nat) : List Nat :=
  (List.range (aMax - 1)).foldr (fun i acc =>
    let a := i + 2
    (List.range (bMax - 1)).map (fun j =>
      let b := j + 2
      a ^ b) ++ acc) []

def distinctCount (aMax bMax : Nat) : Nat :=
  (powers aMax bMax).eraseDups.length

def naive (aMax bMax : Nat) : Nat :=
  distinctCount aMax bMax

example : distinctCount 5 5 = 15 := by
  native_decide

end ProjectEulerStatements.P29
