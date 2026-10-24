import Mathlib.Data.List.Basic
import ProjectEulerStatements.Lib.SqrtPeriods

namespace ProjectEulerStatements.P64

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def periodLen (n : Nat) : Nat :=
  SqrtReducedStates.length n

theorem periodLen_of_square (n : Nat) (square : Nat.sqrt n * Nat.sqrt n = n) :
    periodLen n = 0 := SqrtReducedStates.length_of_square n square

theorem periodLen_positive (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    0 < periodLen n := SqrtReducedStates.length_positive n nonsquare

def countOddPeriods (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc n =>
    let p := periodLen n
    if p % 2 = 1 then acc + 1 else acc) 0

def naive (limit : Nat) : Nat :=
  countOddPeriods limit

end ProjectEulerStatements.P64
