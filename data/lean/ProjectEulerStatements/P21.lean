import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P21

def properDivisors (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (n - 1)).filter (fun d => d ∣ n)

def d (n : Nat) : Nat :=
  (properDivisors n).sum (fun x => x)

def isAmicable (n : Nat) : Prop :=
  let m := d n
  m ≠ n ∧ d m = n

instance : DecidablePred isAmicable := by
  intro n
  unfold isAmicable
  infer_instance

def naive (limit : Nat) : Nat :=
  ((Finset.Icc 1 (limit - 1)).filter (fun n => isAmicable n)).sum (fun n => n)

example : d 220 = 284 := by
  native_decide

example : d 284 = 220 := by
  native_decide

end ProjectEulerStatements.P21
