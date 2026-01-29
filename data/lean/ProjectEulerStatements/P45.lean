import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P45

def tri (n : Nat) : Nat :=
  n * (n + 1) / 2

def pent (n : Nat) : Nat :=
  n * (3 * n - 1) / 2

def hex (n : Nat) : Nat :=
  n * (2 * n - 1)

def isPent (x : Nat) : Bool :=
  (List.range (x + 1)).any (fun n => pent n = x)

def isHex (x : Nat) : Bool :=
  (List.range (x + 1)).any (fun n => hex n = x)

def nextTriPentHex (start limit : Nat) : Nat :=
  let vals := (List.range (limit + 1)).map (fun i => tri (start + i))
  let candidates := vals.filter (fun t => isPent t && isHex t)
  match candidates with
  | [] => 0
  | x :: _ => x

def naive (start limit : Nat) : Nat :=
  nextTriPentHex start limit

example : tri 285 = 40755 := by
  native_decide

example : pent 165 = 40755 := by
  native_decide

example : hex 143 = 40755 := by
  native_decide

end ProjectEulerStatements.P45
