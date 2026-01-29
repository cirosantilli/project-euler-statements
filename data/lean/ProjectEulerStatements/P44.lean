import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P44

def pentagonal (n : Nat) : Nat :=
  n * (3 * n - 1) / 2

def isPentagonal (x : Nat) : Bool :=
  (List.range (x + 1)).any (fun n => pentagonal n = x)

def minDiffPentagonal (limit : Nat) : Nat :=
  let pairs :=
    (List.range (limit + 1)).foldr (fun j acc =>
      (List.range j).foldr (fun k acc2 =>
        let pj := pentagonal j
        let pk := pentagonal k
        if isPentagonal (pj + pk) && isPentagonal (pj - pk) then
          (pj - pk) :: acc2
        else acc2) acc) []
  pairs.foldl Nat.min 0

def naive (limit : Nat) : Nat :=
  minDiffPentagonal limit

example : pentagonal 4 + pentagonal 7 = pentagonal 8 := by
  native_decide

end ProjectEulerStatements.P44
