import Mathlib.Data.Nat.Choose.Basic

namespace ProjectEulerStatements.P15

def naive (n : Nat) : Nat :=
  Nat.choose (2 * n) n

example : naive 2 = 6 := by
  native_decide

end ProjectEulerStatements.P15
