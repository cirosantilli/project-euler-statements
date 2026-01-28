import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P23

def properDivisors (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (n - 1)).filter (fun d => d ∣ n)

def divisorSum (n : Nat) : Nat :=
  (properDivisors n).sum (fun x => x)

def isAbundant (n : Nat) : Prop :=
  divisorSum n > n

instance : DecidablePred isAbundant := by
  intro n
  unfold isAbundant
  infer_instance

def abundantSet (limit : Nat) : Finset Nat :=
  (Finset.Icc 1 limit).filter (fun n => isAbundant n)

def canBeWritten (n limit : Nat) : Prop :=
  ∃ a ∈ abundantSet limit, ∃ b ∈ abundantSet limit, a + b = n

noncomputable def naive (limit : Nat) : Nat := by
  classical
  exact ((Finset.Icc 1 limit).filter (fun n => ¬ canBeWritten n limit)).sum (fun n => n)

example : isAbundant 12 := by
  native_decide

example : (24 : Nat) = 12 + 12 := by
  native_decide

end ProjectEulerStatements.P23
