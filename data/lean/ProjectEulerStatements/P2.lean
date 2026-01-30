import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P2

-- HELPERS

open scoped BigOperators

def fib : Nat -> Nat
  | 0       => 1
  | 1       => 2
  | n + 2   => fib (n) + fib (n + 1)

theorem fib_ge_succ (n : Nat) : n + 1 ≤ fib n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      simp [fib]
  | succ n =>
      cases n with
      | zero =>
          simp [fib]
      | succ n =>
          have ih_n : n + 1 ≤ fib n := ih n (by omega)
          have ih_n1 : n + 2 ≤ fib (n + 1) := ih (n + 1) (by omega)
          have hsum : (n + 1) + (n + 2) ≤ fib n + fib (n + 1) :=
            add_le_add ih_n ih_n1
          have hstep : n + 3 ≤ (n + 1) + (n + 2) := by omega
          have h' : n + 3 ≤ fib n + fib (n + 1) := le_trans hstep hsum
          simpa [fib, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h'

theorem fib_eq_nat_fib_aux :
    ∀ n, fib n = Nat.fib (n + 2) ∧ fib (n + 1) = Nat.fib (n + 3) := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp [fib]
      · simp [fib, Nat.fib_add_two]
  | succ n ih =>
      constructor
      · exact ih.2
      · calc
          fib (n + 2) = fib n + fib (n + 1) := by
            simp [fib]
          _ = Nat.fib (n + 2) + Nat.fib (n + 3) := by
            simp [ih.1, ih.2]
          _ = Nat.fib (n + 4) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Nat.fib_add_two (n := n + 2)).symm

theorem fib_eq_nat_fib (n : Nat) : fib n = Nat.fib (n + 2) :=
  (fib_eq_nat_fib_aux n).1

-- MAIN

/-- Sum of the even-valued Fibonacci numbers which do not exceed `n` -/
def naive (n : Nat) : Nat :=
  let rec go (i total : Nat) : Nat :=
    let f := fib i
    if f <= n then
      go (i + 1) (if f % 2 = 0 then total + f else total)
    else
      total
  termination_by n + 1 - i
  decreasing_by
    have hi' : i + 1 ≤ n := le_trans (fib_ge_succ i) (by simpa using ‹_›)
    omega
  go 0 0

noncomputable def naive2 (n : Nat) : Nat := by
  classical
  let S : Set Nat := {x | (∃ i, fib i = x) ∧ x ≤ n ∧ x % 2 = 0}
  have hfin : S.Finite := by
    refine (Set.finite_le_nat n).subset ?_
    intro x hx
    exact hx.2.1
  exact ∑ x ∈ hfin.toFinset, x

theorem naive_eq_naive2 (n : Nat) : naive n = naive2 n := sorry

end ProjectEulerStatements.P2
