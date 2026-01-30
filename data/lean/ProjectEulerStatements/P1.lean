import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P1

/-- Sum of all the multiples of 3 or 5 or below `n`. -/
def naive : Nat -> Nat
  | 0       => 0
  | n + 1   =>
      let s := naive n
      if 3 ∣ n ∨ 5 ∣ n then s + n else s

def naive2 (max : Nat) : Nat :=
  ∑ x ∈ ((Finset.range max).filter (fun n => (3 ∣ n) ∨ (5 ∣ n))), x

example : naive (10) = 23 := by native_decide

theorem naive_eq_naive2 (max : Nat) : naive max = naive2 max := by
  induction max with
  | zero =>
      simp [naive, naive2]
  | succ n ih =>
      by_cases hp : (3 ∣ n ∨ 5 ∣ n)
      · have hn : n ∉ (Finset.range n).filter (fun x => (3 ∣ x) ∨ (5 ∣ x)) := by
          simp
        simp [naive, naive2, Finset.range_add_one, Finset.filter_insert, ih, hp, hn,
          Finset.sum_insert, add_comm]
      · simp [naive, naive2, Finset.range_add_one, Finset.filter_insert, ih, hp]

end ProjectEulerStatements.P1
