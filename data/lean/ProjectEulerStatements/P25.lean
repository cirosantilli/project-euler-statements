import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P25

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => fib (n + 2) + fib (n + 1)

def numDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).length

def firstFibWithDigits (digits fuel : Nat) : Nat :=
  let rec go (i a b fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if numDigits a ≥ digits then
          i
        else
          go (i + 1) b (a + b) fuel
  go 1 1 1 fuel

def naive (digits fuel : Nat) : Nat :=
  firstFibWithDigits digits fuel

example : fib 12 = 144 := by
  native_decide

example : firstFibWithDigits 3 20 = 12 := by
  native_decide

end ProjectEulerStatements.P25
