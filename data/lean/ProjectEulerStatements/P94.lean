import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P94

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def areaIsInt (a b c : Nat) : Bool :=
  let s := a + b + c
  if s % 2 = 1 then false else
    let p := s / 2
    let area2 := p * (p - a) * (p - b) * (p - c)
    isSquare area2

def sumPerimeters (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc a =>
    let b := a
    let c1 := a - 1
    let c2 := a + 1
    let acc1 := if decide (a > 1 ∧ c1 > 0) && areaIsInt a b c1 then acc + (a + b + c1) else acc
    let acc2 := if areaIsInt a b c2 then acc1 + (a + b + c2) else acc1
    acc2) 0

def naive (limit : Nat) : Nat :=
  sumPerimeters limit

example : areaIsInt 5 5 6 = true := by
  native_decide

end ProjectEulerStatements.P94
