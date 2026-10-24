import ProjectEulerStatements.P31
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Basic

/-! Positive-coin counting and the ascending dynamic-programming frontier.

The reference consumes coins from the head, whereas an imperative table processes
them from left to right. Permutation invariance connects these two orders without
assuming that the denominations are distinct or sorted. -/
namespace ProjectEulerStatements.CoinChange
open P31

@[simp] theorem countWaysBound_zero (cs : List Nat) : countWaysBound 0 cs = 1 := by
  rw [countWaysBound]

@[simp] theorem countWaysBound_nil (amount : Nat) :
    countWaysBound amount [] = if amount = 0 then 1 else 0 := by
  cases amount <;> simp [countWaysBound]

/-- The current coin is either unused or used at least once. -/
theorem countWaysBound_cons (amount c : Nat) (cs : List Nat) (positive : 0 < c) :
    countWaysBound amount (c :: cs) = countWaysBound amount cs +
      if c ≤ amount then countWaysBound (amount - c) (c :: cs) else 0 := by
  cases amount with
  | zero => simp [Nat.not_le.mpr positive]
  | succ amount =>
      rw [countWaysBound] <;> try omega
      have nonzero : c ≠ 0 := Nat.ne_of_gt positive
      by_cases enough : c ≤ amount + 1
      · simp only [nonzero, ↓reduceDIte, Nat.not_lt.mpr enough, enough, ↓reduceIte,
          Nat.add_comm]
      · simp only [nonzero, ↓reduceDIte, Nat.lt_of_not_ge enough, enough, ↓reduceIte,
          Nat.add_zero]

/-- Equal rows remain equal when one positive denomination is added. -/
theorem countWaysBound_cons_congr (c : Nat) (cs ds : List Nat) (positive : 0 < c)
    (equal : ∀ amount, countWaysBound amount cs = countWaysBound amount ds)
    (amount : Nat) : countWaysBound amount (c :: cs) = countWaysBound amount (c :: ds) := by
  induction amount using Nat.strong_induction_on with
  | h amount ih =>
      rw [countWaysBound_cons amount c cs positive,
        countWaysBound_cons amount c ds positive, equal amount]
      by_cases enough : c ≤ amount
      · simp only [if_pos enough]
        rw [ih (amount - c) (by omega)]
      · simp only [if_neg enough]

/-- Swapping adjacent positive denominations preserves the number of choices. -/
theorem countWaysBound_swap (c d : Nat) (cs : List Nat)
    (cPositive : 0 < c) (dPositive : 0 < d) (amount : Nat) :
    countWaysBound amount (c :: d :: cs) = countWaysBound amount (d :: c :: cs) := by
  induction amount using Nat.strong_induction_on with
  | h amount ih =>
      have cd := countWaysBound_cons amount c (d :: cs) cPositive
      have dc := countWaysBound_cons amount d (c :: cs) dPositive
      have cOnly := countWaysBound_cons amount c cs cPositive
      have dOnly := countWaysBound_cons amount d cs dPositive
      by_cases cEnough : c ≤ amount
      · by_cases dEnough : d ≤ amount
        · have smallerC := ih (amount - c) (by omega)
          have smallerD := ih (amount - d) (by omega)
          have afterC := countWaysBound_cons (amount - c) d (c :: cs) dPositive
          have afterD := countWaysBound_cons (amount - d) c (d :: cs) cPositive
          simp only [if_pos cEnough] at cd cOnly
          simp only [if_pos dEnough] at dc dOnly
          by_cases both : c + d ≤ amount
          · have dAfterC : d ≤ amount - c := by omega
            have cAfterD : c ≤ amount - d := by omega
            simp only [if_pos dAfterC] at afterC
            simp only [if_pos cAfterD] at afterD
            have subtraction : amount - c - d = amount - d - c := by omega
            have smallerBoth := ih (amount - c - d) (by omega)
            rw [← subtraction] at afterD
            omega
          · have dAfterC : ¬ d ≤ amount - c := by omega
            have cAfterD : ¬ c ≤ amount - d := by omega
            simp only [if_neg dAfterC, Nat.add_zero] at afterC
            simp only [if_neg cAfterD, Nat.add_zero] at afterD
            omega
        · have cAfterD : ¬ d ≤ amount - c := by omega
          have afterC := countWaysBound_cons (amount - c) d cs dPositive
          have smallerC := ih (amount - c) (by omega)
          have afterC' := countWaysBound_cons (amount - c) d (c :: cs) dPositive
          simp only [if_pos cEnough] at cd cOnly
          simp only [if_neg dEnough, Nat.add_zero] at dc dOnly
          simp only [if_neg cAfterD, Nat.add_zero] at afterC afterC'
          omega
      · by_cases dEnough : d ≤ amount
        · have dAfterC : ¬ c ≤ amount - d := by omega
          have smallerD := ih (amount - d) (by omega)
          have afterD := countWaysBound_cons (amount - d) c (d :: cs) cPositive
          simp only [if_neg cEnough, Nat.add_zero] at cd cOnly
          simp only [if_pos dEnough] at dc dOnly
          simp only [if_neg dAfterC, Nat.add_zero] at afterD
          omega
        · simp only [if_neg cEnough, Nat.add_zero] at cd cOnly
          simp only [if_neg dEnough, Nat.add_zero] at dc dOnly
          omega

theorem countWaysBound_perm {cs ds : List Nat} (permutation : cs.Perm ds)
    (positive : ∀ c ∈ cs, 0 < c) (amount : Nat) :
    countWaysBound amount cs = countWaysBound amount ds := by
  revert positive amount
  induction permutation with
  | nil => intros; rfl
  | @cons c cs ds permutation ih =>
      intro positive amount
      exact countWaysBound_cons_congr c cs ds (positive c (by simp))
        (ih (fun d member => positive d (by simp [member]))) amount
  | swap c d cs =>
      intro positive amount
      exact countWaysBound_swap d c cs (positive d (by simp)) (positive c (by simp)) amount
  | @trans cs ds es first second ihFirst ihSecond =>
      intro positive amount
      exact (ihFirst positive amount).trans
        (ihSecond (fun c member => positive c (first.mem_iff.mpr member)) amount)

theorem countWaysBound_reverse (amount : Nat) (cs : List Nat)
    (positive : ∀ c ∈ cs, 0 < c) :
    countWaysBound amount cs.reverse = countWaysBound amount cs := by
  exact countWaysBound_perm (List.reverse_perm cs)
    (fun c member => positive c (List.mem_reverse.mp member)) amount

/-- Values below `first` already include the current denomination. -/
def frontier (c : Nat) (processed : List Nat) (first amount : Nat) : Nat :=
  if amount < first then countWaysBound amount (c :: processed)
  else countWaysBound amount processed

theorem frontier_start (c : Nat) (processed : List Nat) (amount : Nat)
    (positive : 0 < c) :
    frontier c processed c amount = countWaysBound amount processed := by
  unfold frontier
  split
  next smaller =>
    rw [countWaysBound_cons amount c processed positive]
    simp only [if_neg (Nat.not_le.mpr smaller), Nat.add_zero]
  next => rfl

/-- One in-place addition advances the frontier by one position. -/
theorem frontier_step (c : Nat) (processed : List Nat) (first amount : Nat)
    (positive : 0 < c) (started : c ≤ first) :
    frontier c processed (first + 1) amount =
      if amount = first then
        frontier c processed first first + frontier c processed first (first - c)
      else frontier c processed first amount := by
  by_cases current : amount = first
  · subst amount
    have smaller : first - c < first := by omega
    simp only [frontier, Nat.lt_succ_self, if_true, Nat.lt_irrefl, if_false,
      smaller]
    simpa only [if_pos started] using countWaysBound_cons first c processed positive
  · have same : (amount < first + 1) = (amount < first) := by
      apply propext
      omega
    simp only [if_neg current, frontier, same]

theorem frontier_complete (c : Nat) (processed : List Nat) (target amount : Nat)
    (bounded : amount ≤ target) :
    frontier c processed (target + 1) amount = countWaysBound amount (c :: processed) := by
  exact if_pos (by omega)

end ProjectEulerStatements.CoinChange
