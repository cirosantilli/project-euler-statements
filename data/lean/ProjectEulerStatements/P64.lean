import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P64

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def periodLenAux (n a0 : Nat) (m d a : Nat) : Nat :=
  let rec go (m d a steps : Nat) : Nat :=
    match steps with
    | 0 => 0
    | steps + 1 =>
        let m' := d * a - m
        let d' := (n - m' * m') / d
        let a' := (a0 + m') / d'
        if a' = 2 * a0 then
          1
        else
          1 + go m' d' a' steps
  go m d a (n + 1)

def periodLen (n : Nat) : Nat :=
  let a0 := Nat.sqrt n
  if isSquare n then 0 else periodLenAux n a0 0 1 a0

def countOddPeriods (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc n =>
    let p := periodLen n
    if p % 2 = 1 then acc + 1 else acc) 0

def naive (limit : Nat) : Nat :=
  countOddPeriods limit

example : countOddPeriods 13 = 4 := by
  native_decide

end ProjectEulerStatements.P64
