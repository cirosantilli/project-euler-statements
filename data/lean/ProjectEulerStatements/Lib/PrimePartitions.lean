import ProjectEulerStatements.Lib.CoinChange
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Find

/-! Prime partition counts grow without a search cutoff, already using only parts two and three. -/
namespace ProjectEulerStatements.PrimePartitions
open P31 CoinChange
set_option Elab.async false

theorem countWaysBound_sublist (amount : Nat) (cs ds : List Nat) (included : cs.Sublist ds)
    (positive : ∀ c ∈ ds, 0 < c) : countWaysBound amount cs ≤ countWaysBound amount ds := by
  induction amount using Nat.strong_induction_on generalizing cs ds with
  | h amount smaller =>
      induction included with
      | slnil => exact Nat.le_refl _
      | @cons cs ds c included ih =>
          have before := ih (fun p member => positive p (by simp [member]))
          rw [countWaysBound_cons amount c ds (positive c (by simp))]
          omega
      | @cons_cons cs ds c included ih =>
          have cPositive := positive c (by simp)
          have tailPositive : ∀ p ∈ ds, 0 < p := fun p member => positive p (by simp [member])
          rw [countWaysBound_cons amount c cs cPositive,
            countWaysBound_cons amount c ds cPositive]
          by_cases enough : c ≤ amount
          · simp only [if_pos enough]
            exact Nat.add_le_add (ih tailPositive)
              (smaller (amount-c) (by omega) _ _ (.cons_cons c included) positive)
          · simp only [if_neg enough, Nat.add_zero]
            exact ih tailPositive

theorem countWaysBound_single_multiple (c k : Nat) (positive : 0 < c) :
    countWaysBound (c*k) [c] = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, countWaysBound_cons _ _ _ positive]
      have nonzero : c*k+c ≠ 0 := by omega
      have enough : c ≤ c*k+c := by omega
      simp only [countWaysBound_nil, if_neg nonzero, if_pos enough, Nat.zero_add,
        Nat.add_sub_cancel_right, ih]

theorem two_three_growth (k : Nat) : k+1 ≤ countWaysBound (6*k) [3, 2] := by
  induction k with
  | zero => simp
  | succ k ih =>
      have first := countWaysBound_cons (6*(k+1)) 3 [2] (by omega)
      have second := countWaysBound_cons (6*k+3) 3 [2] (by omega)
      have single := countWaysBound_single_multiple 2 (3*(k+1)) (by omega)
      have even : 2*(3*(k+1)) = 6*(k+1) := by omega
      rw [even] at single
      simp only [if_pos (show 3 ≤ 6*(k+1) by omega)] at first
      simp only [if_pos (show 3 ≤ 6*k+3 by omega)] at second
      have afterFirst : 6*(k+1)-3 = 6*k+3 := by omega
      have afterSecond : 6*k+3-3 = 6*k := by omega
      rw [afterFirst, single] at first
      rw [afterSecond] at second
      omega

def primesUpTo (n : Nat) : List Nat :=
  (List.range (n+1)).filter (fun p => decide (Nat.Prime p))

theorem primesUpTo_positive (n : Nat) : ∀ p ∈ primesUpTo n, 0 < p := by
  intro p member
  have prime : Nat.Prime p := of_decide_eq_true (List.mem_filter.mp member).2
  exact prime.pos

theorem two_three_sublist (n : Nat) (large : 3 ≤ n) : [2, 3].Sublist (primesUpTo n) := by
  have split : List.range (n+1) = [0, 1, 2, 3] ++ List.range' 4 (n-3) := by
    rw [List.range_eq_range', show n+1 = 4+(n-3) by omega, ← List.range'_append_1]
    rfl
  have front : primesUpTo n = [2, 3] ++
      ((List.range' 4 (n-3)).filter (fun p => decide (Nat.Prime p))) := by
    simp [primesUpTo, split, Nat.not_prime_zero, Nat.not_prime_one,
      Nat.prime_two, Nat.prime_three]
  rw [front]
  exact List.sublist_append_left _ _

def count (n : Nat) : Nat := countWaysBound n (primesUpTo n)

theorem count_growth (k : Nat) (positive : 0 < k) : k+1 ≤ count (6*k) := by
  have small := two_three_growth k
  rw [countWaysBound_swap 3 2 [] (by omega) (by omega)] at small
  have large := countWaysBound_sublist (6*k) [2, 3] (primesUpTo (6*k))
    (two_three_sublist _ (by omega)) (primesUpTo_positive _)
  exact small.trans large

def Over (target : Int) (n : Nat) : Prop := 2 ≤ n ∧ target < (count n : Int)

instance (target : Int) (n : Nat) : Decidable (Over target n) := by
  unfold Over
  infer_instance

/-- At multiples of six, the two-prime family already exceeds every signed threshold. -/
theorem exists_over (target : Int) : ∃ n : Nat, Over target n := by
  refine ⟨6*(target.toNat+1), ?_, ?_⟩
  · omega
  · have lower := count_growth (target.toNat+1) (by omega)
    omega

def answer (target : Int) : Nat := Nat.find (exists_over target)

theorem answer_spec (target : Int) : Over target (answer target) :=
  Nat.find_spec (exists_over target)

theorem answer_le (target : Int) (n : Nat) (over : Over target n) : answer target ≤ n :=
  Nat.find_min' (exists_over target) over

theorem before_answer (target : Int) (n : Nat) (lower : 2 ≤ n) (before : n < answer target) :
    (count n : Int) ≤ target := by
  by_contra rejected
  have least := answer_le target n ⟨lower, by omega⟩
  omega

end ProjectEulerStatements.PrimePartitions
