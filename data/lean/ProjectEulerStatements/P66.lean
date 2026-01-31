import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P66

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def minimalX (d : Nat) : Nat :=
  if isSquare d then 0 else
  let bound := d ^ 4 + 1
  let rec go (y steps : Nat) : Nat :=
    match steps with
    | 0 => 0
    | steps + 1 =>
        let x2 := d * y * y + 1
        let x := Nat.sqrt x2
        if x * x = x2 then x else go (y + 1) steps
  go 1 bound

def bestD (limit : Nat) : Nat :=
  let rec go (d bestD bestX steps : Nat) : Nat :=
    match steps with
    | 0 => bestD
    | steps + 1 =>
        if d > limit then bestD
        else
          let x := minimalX d
          if x > bestX then go (d + 1) d x steps else go (d + 1) bestD bestX steps
  go 2 0 0 (limit + 1)

def naive (limit : Nat) : Nat :=
  bestD limit

example : minimalX 13 = 649 := by
  native_decide

example : bestD 7 = 5 := by
  native_decide

end ProjectEulerStatements.P66
