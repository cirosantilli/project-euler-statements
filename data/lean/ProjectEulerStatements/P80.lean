import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P80

def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def sqrtDigitsSum (n digits : Nat) : Nat :=
  if isSquare n then 0 else
    let scale := 10 ^ (2 * (digits - 1))
    let scaled := Nat.sqrt (n * scale)
    digitSum scaled

def totalSum (limit digits : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc n => acc + sqrtDigitsSum n digits) 0

def naive (limit digits : Nat) : Nat :=
  totalSum limit digits

example : sqrtDigitsSum 2 100 = 475 := by
  native_decide

end ProjectEulerStatements.P80
