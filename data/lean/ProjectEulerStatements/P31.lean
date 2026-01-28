import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P31

def coins : List Nat := [1, 2, 5, 10, 20, 50, 100, 200]

def countWaysBound : Nat -> List Nat -> Nat -> Nat
  | 0, _, _ => 1
  | _, [], _ => 0
  | amt, c :: cs, fuel =>
      match fuel with
      | 0 => 0
      | fuel + 1 =>
          if amt < c then
            countWaysBound amt cs fuel
          else
            countWaysBound (amt - c) (c :: cs) fuel +
              countWaysBound amt cs fuel

def naive (amt fuel : Nat) : Nat :=
  countWaysBound amt coins fuel

example : 100 + 50 + 20 + 20 + 5 + 2 + 1 + 1 + 1 = 200 := by
  native_decide

end ProjectEulerStatements.P31
