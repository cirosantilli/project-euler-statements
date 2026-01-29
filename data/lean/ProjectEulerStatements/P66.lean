import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P66

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def minimalX (d fuel : Nat) : Nat :=
  if isSquare d then 0 else
  let rec go (y fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        let x2 := d * y * y + 1
        let x := Nat.sqrt x2
        if x * x = x2 then x else go (y + 1) fuel
  go 1 fuel

def bestD (limit fuel : Nat) : Nat :=
  let rec go (d bestD bestX fuel : Nat) : Nat :=
    match fuel with
    | 0 => bestD
    | fuel + 1 =>
        if d > limit then bestD
        else
          let x := minimalX d fuel
          if x > bestX then go (d + 1) d x fuel else go (d + 1) bestD bestX fuel
  go 2 0 0 fuel

def naive (limit fuel : Nat) : Nat :=
  bestD limit fuel

example : minimalX 13 1000 = 649 := by
  native_decide

example : bestD 7 200 = 5 := by
  native_decide

end ProjectEulerStatements.P66
