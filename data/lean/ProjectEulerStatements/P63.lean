import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P63

def numDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).length

def countNDigitPowers (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc n =>
    let count :=
      (List.range 10).foldl (fun acc2 a =>
        if a = 0 then acc2 else
        if numDigits (a ^ n) = n then acc2 + 1 else acc2) 0
    acc + count) 0

def naive (limit : Nat) : Nat :=
  countNDigitPowers limit

example : numDigits (7 ^ 5) = 5 := by
  native_decide

example : numDigits (8 ^ 9) = 9 := by
  native_decide

end ProjectEulerStatements.P63
