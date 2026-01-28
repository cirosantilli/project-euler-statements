import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P22

def letterValue (c : Char) : Nat :=
  let n := c.toNat
  let a := 'A'.toNat
  if a ≤ n ∧ n ≤ 'Z'.toNat then n - a + 1 else 0

def nameValue (s : String) : Nat :=
  s.data.foldl (fun acc c => acc + letterValue c) 0

def nameScore (pos : Nat) (name : String) : Nat :=
  pos * nameValue name

def enumFrom {α : Type} : Nat -> List α -> List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: enumFrom (n + 1) xs

def naive (names : List String) : Nat :=
  let sorted := names.mergeSort (fun a b => decide (a ≤ b))
  (enumFrom 1 sorted).foldl (fun acc p => acc + nameScore p.1 p.2) 0

example : nameValue "COLIN" = 53 := by
  native_decide

example : nameScore 938 "COLIN" = 49714 := by
  native_decide

end ProjectEulerStatements.P22
