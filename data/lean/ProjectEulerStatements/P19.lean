import Mathlib.Data.List.Basic
import Mathlib.Tactic

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

structure Date where
  year : Nat
  month : Nat
  day : Nat
  month_pos : 0 < month
  month_le : month ≤ 12
  day_pos : 0 < day
  day_le : day ≤ daysInMonth year month

def mkDate (year month day : Nat)
    (month_pos : 0 < month) (month_le : month ≤ 12)
    (day_pos : 0 < day) (day_le : day ≤ daysInMonth year month) : Date :=
  { year, month, day, month_pos, month_le, day_pos, day_le }

def mkFirstOfMonth (year month : Nat)
    (month_pos : 0 < month) (month_le : month ≤ 12) : Date :=
  { year, month, day := 1,
    month_pos, month_le,
    day_pos := by decide,
    day_le := by
      have h1 : 1 ≤ month := Nat.succ_le_iff.mp month_pos
      interval_cases month <;>
        (simp [daysInMonth, isLeap] <;>
          try
            (by_cases h :
                year % 4 = 0 ∧ (¬year % 100 = 0 ∨ year % 400 = 0) <;>
              simp [h])) }

def daysInYear (y : Nat) : Nat :=
  if isLeap y then 366 else 365

def daysBeforeYear (y : Nat) : Nat :=
  (List.range (y - 1900)).foldl (fun acc i => acc + daysInYear (1900 + i)) 0

def daysBeforeMonth (y m : Nat) : Nat :=
  (List.range (m - 1)).foldl (fun acc i => acc + daysInMonth y (i + 1)) 0

def dayOfWeek (y m d : Nat) : Nat :=
  (daysBeforeYear y + daysBeforeMonth y m + (d - 1)) % 7

-- 0 = Monday, 6 = Sunday

def dateToDays (d : Date) : Nat :=
  daysBeforeYear d.year + daysBeforeMonth d.year d.month + (d.day - 1)

def countSundaysBetween (startDate endDate : Date) : Nat :=
  let startDays := dateToDays startDate
  let endDays := dateToDays endDate
  (List.range (endDate.year - startDate.year + 1)).foldl
    (fun acc i =>
      let y := startDate.year + i
      acc + (List.range 12).foldl
        (fun acc2 j =>
          let m := j + 1
          let days := daysBeforeYear y + daysBeforeMonth y m
          if startDays ≤ days ∧ days ≤ endDays ∧ dayOfWeek y m 1 = 6 then
            acc2 + 1
          else
            acc2)
        0)
    0

def naive (startDate endDate : Date) : Nat :=
  countSundaysBetween startDate endDate

example : dayOfWeek 1900 1 1 = 0 := by
  native_decide

end ProjectEulerStatements.P19
