import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P31

def coins : List Nat := [1, 2, 5, 10, 20, 50, 100, 200]

def countWaysBound (amt : Nat) (cs : List Nat) : Nat :=
  match amt, cs with
  | 0, _ => 1
  | _, [] => 0
  | amt, c :: cs =>
      if h0 : c = 0 then
        (by
          have _ := h0
          exact countWaysBound amt cs)
      else if hlt : amt < c then
        (by
          have _ := hlt
          exact countWaysBound amt cs)
      else
        countWaysBound (amt - c) (c :: cs) +
          countWaysBound amt cs
termination_by amt + cs.length
decreasing_by
  all_goals
    simp
    try omega

def naive (amt : Nat) : Nat :=
  countWaysBound amt coins

example : 100 + 50 + 20 + 20 + 5 + 2 + 1 + 1 + 1 = 200 := by
  native_decide

end ProjectEulerStatements.P31
