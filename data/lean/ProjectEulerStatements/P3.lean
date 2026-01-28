import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P3

def primeFactorSet (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun k => 2 ≤ k ∧ k ∣ n ∧ Nat.Prime k)

def naive (n : Nat) : Nat :=
  if h : (primeFactorSet n).Nonempty then
    (primeFactorSet n).max' h
  else
    0

example : naive 13195 = 29 := by
  native_decide

end ProjectEulerStatements.P3
