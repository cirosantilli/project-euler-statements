import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P46

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def isOddComposite (n : Nat) : Bool :=
  n % 2 = 1 && !isPrime n && n > 1

def canBeWritten (n : Nat) : Bool :=
  (List.range n).any (fun p =>
    if isPrime p then
      (List.range n).any (fun k => p + 2 * k^2 = n)
    else false)

def smallestCounterexample (limit : Nat) : Nat :=
  match (List.find? (fun n => isOddComposite n && !canBeWritten n) (List.range limit)) with
  | some n => n
  | none => 0

def naive (limit : Nat) : Nat :=
  smallestCounterexample limit

example : 9 = 7 + 2 * 1^2 := by
  native_decide

example : 33 = 31 + 2 * 1^2 := by
  native_decide

end ProjectEulerStatements.P46
