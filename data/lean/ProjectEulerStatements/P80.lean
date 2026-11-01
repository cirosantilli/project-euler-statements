import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Sqrt

namespace ProjectEulerStatements.P80

def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def integerWidth (n : Nat) : Nat :=
  (toString (Nat.sqrt n)).length

def sqrtPrefix (n digits : Nat) : Nat :=
  if digits < integerWidth n then
    Nat.sqrt n / 10 ^ (integerWidth n - digits)
  else
    Nat.sqrt (n * 10 ^ (2 * (digits - integerWidth n)))

def sqrtDigitsSum (n digits : Nat) : Nat :=
  if isSquare n then 0 else digitSum (sqrtPrefix n digits)

def totalSum (limit digits : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc n => acc + sqrtDigitsSum n digits) 0

def naive (limit digits : Nat) : Nat :=
  totalSum limit digits

end ProjectEulerStatements.P80
