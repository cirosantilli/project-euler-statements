import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P65

def coeffE (k : Nat) : Nat :=
  if k = 0 then 2
  else
    if k % 3 = 2 then 2 * (k / 3 + 1) else 1

def coeffs (n : Nat) : List Nat :=
  (List.range n).map coeffE

def convergentNum (n : Nat) : Nat :=
  let as := coeffs n
  let rec go (l : List Nat) (p0 p1 : Nat) : Nat :=
    match l with
    | [] => p1
    | a :: tl =>
        let p := a * p1 + p0
        go tl p1 p
  go as 0 1

def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

def naive (n : Nat) : Nat :=
  digitSum (convergentNum n)

example : digitSum (convergentNum 10) = 17 := by
  native_decide

end ProjectEulerStatements.P65
