import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P19

def isLeap (y : Nat) : Bool :=
  (y % 4 = 0) && ((y % 100 ≠ 0) || (y % 400 = 0))

def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 1 => 31
  | 2 => if isLeap y then 29 else 28
  | 3 => 31
  | 4 => 30
  | 5 => 31
  | 6 => 30
  | 7 => 31
  | 8 => 31
  | 9 => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _ => 0

def daysInYear (y : Nat) : Nat :=
  if isLeap y then 366 else 365

def daysBeforeYear (y : Nat) : Nat :=
  (List.range (y - 1900)).foldl (fun acc i => acc + daysInYear (1900 + i)) 0

def daysBeforeMonth (y m : Nat) : Nat :=
  (List.range (m - 1)).foldl (fun acc i => acc + daysInMonth y (i + 1)) 0

def dayOfWeek (y m d : Nat) : Nat :=
  (daysBeforeYear y + daysBeforeMonth y m + (d - 1)) % 7

-- 0 = Monday, 6 = Sunday

def countSundays : Nat :=
  (List.range (2000 - 1901 + 1)).foldl
    (fun acc i =>
      let y := 1901 + i
      acc + (List.range 12).foldl
        (fun acc2 j =>
          let m := j + 1
          if dayOfWeek y m 1 = 6 then acc2 + 1 else acc2)
        0)
    0

def naive : Nat :=
  countSundays

example : dayOfWeek 1900 1 1 = 0 := by
  native_decide

end ProjectEulerStatements.P19
