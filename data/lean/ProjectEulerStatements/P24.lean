import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P24

def lexLE : List Nat -> List Nat -> Bool
  | [], _ => true
  | _ , [] => false
  | a :: as, b :: bs => if a = b then lexLE as bs else decide (a ≤ b)

def sortPerms (l : List (List Nat)) : List (List Nat) :=
  l.mergeSort (fun a b => lexLE a b)

def nthPerm (l : List Nat) (idx : Nat) : List Nat :=
  match (sortPerms l.permutations)[idx - 1]? with
  | some p => p
  | none => []

def naive (digits : List Nat) (idx : Nat) : List Nat :=
  nthPerm digits idx

example : naive [0, 1, 2] 1 = [0, 1, 2] := by
  native_decide

example : naive [0, 1, 2] 6 = [2, 1, 0] := by
  native_decide

end ProjectEulerStatements.P24
