import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P5

/-- Smallest number that is evenly divisible by all of the numbers from 1 to n. -/
def naive (n : Nat) : Nat :=
  (Finset.Icc 1 n).lcm (fun x => x)

example : naive 10 = 2520 := by
  native_decide

end ProjectEulerStatements.P5
