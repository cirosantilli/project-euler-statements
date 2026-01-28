import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P30

def digitPowerSum (p n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + d ^ p) 0

def sumPowerDigits (p limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl
    (fun acc n =>
      if n = 1 then acc
      else if digitPowerSum p n = n then acc + n else acc)
    0

def naive (p limit : Nat) : Nat :=
  sumPowerDigits p limit

example : sumPowerDigits 4 100000 = 19316 := by
  native_decide

end ProjectEulerStatements.P30
