import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P86

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def countCuboids (m : Nat) : Nat :=
  let rec go (a b c acc : Nat) : Nat :=
    if a = 0 then acc else
      if b = 0 then go (a - 1) m m acc else
        if c = 0 then go a (b - 1) m acc else
          let x := a
          let y := b
          let z := c
          let ok := isSquare ((x + y) * (x + y) + z * z)
          let acc' := if x ≤ y ∧ y ≤ z ∧ ok then acc + 1 else acc
          go a b (c - 1) acc'
  go m m m 0

def naive (m : Nat) : Nat :=
  countCuboids m

example : countCuboids 100 = 2060 := by
  native_decide

example : countCuboids 99 = 1975 := by
  native_decide

end ProjectEulerStatements.P86
