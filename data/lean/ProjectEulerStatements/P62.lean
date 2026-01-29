import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P62

def digitsKey (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

def cubePermCount (limit n : Nat) : Nat :=
  let cubes := (List.range (limit + 1)).map (fun i => i ^ 3)
  let key := digitsKey (n ^ 3)
  (cubes.filter (fun c => digitsKey c = key)).length

def smallestCubeWithPerms (limit target : Nat) : Nat :=
  match (List.find? (fun n => cubePermCount limit n = target) (List.range (limit + 1))) with
  | some n => n ^ 3
  | none => 0

def naive (limit target : Nat) : Nat :=
  smallestCubeWithPerms limit target

example : cubePermCount 500 345 = 3 := by
  native_decide

end ProjectEulerStatements.P62
