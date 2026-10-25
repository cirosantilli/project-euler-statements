import ProjectEulerStatements.Lib.TotientPermutation
import ProjectEulerStatements.Lib.TotientMaximum
import Mathlib.Data.List.Range

/-! Strict ratio minimization over the eligible decimal totient permutations. -/
namespace ProjectEulerStatements.TotientPermutation
open TotientMaximum (ratio ratio_lt_iff)
set_option Elab.async false

def eligible (n : Nat) : Prop := 1 < n ∧ isPermutation n n.totient = true

instance (n : Nat) : Decidable (eligible n) := inferInstanceAs
  (Decidable (1 < n ∧ isPermutation n n.totient = true))

def better (a b : Nat) : Bool :=
  if a.totient = 0 ∨ b.totient = 0 then false
  else decide (a * b.totient < b * a.totient)

def visit (best n : Nat) : Nat :=
  if eligible n then if best = 0 ∨ better n best then n else best else best

def bestUpTo : Nat → Nat
  | 0 => 0
  | n + 1 => visit (bestUpTo n) (n + 1)

def result (limit : Int) : Nat := bestUpTo limit.toNat

/-- The zero sentinel is used exactly when the candidate range is empty. -/
structure Best (limit value : Nat) : Prop where
  selected : value ≠ 0 → eligible value ∧ value ≤ limit
  empty : value = 0 → ∀ n, n ≤ limit → ¬ eligible n
  minimizes : value ≠ 0 → ∀ n, n ≤ limit → eligible n → ratio value ≤ ratio n
  least : value ≠ 0 → ∀ n, n ≤ limit → eligible n → ratio value = ratio n → value ≤ n

theorem better_iff (a b : Nat) (aPositive : 0 < a) (bPositive : 0 < b) :
    better a b = true ↔ ratio a < ratio b := by
  have aPhi := (Nat.totient_pos.mpr aPositive).ne'
  have bPhi := (Nat.totient_pos.mpr bPositive).ne'
  simp only [better, aPhi, bPhi, or_self, if_false, decide_eq_true_eq,
    ratio_lt_iff a b aPositive bPositive]

theorem visit_zero (best : Nat) : visit best 0 = best := by
  have absent : ¬ eligible 0 := by rintro ⟨h, _⟩; omega
  simp only [visit, if_neg absent]

theorem visit_new (limit best : Nat) (previous : Best limit best)
    (accepted : eligible (limit + 1)) :
    visit best (limit + 1) =
      if best = 0 then limit + 1
      else if ratio (limit + 1) < ratio best then limit + 1 else best := by
  by_cases zero : best = 0
  · simp only [visit, if_pos accepted, zero, true_or, if_true]
  · have positive : 0 < best := Nat.zero_lt_one.trans (previous.selected zero).1.1
    simp only [visit, if_pos accepted, zero, false_or, if_false,
      better_iff (limit + 1) best (by omega) positive]

/-- A strict improvement scan retains the smallest value on ratio ties. -/
theorem best_step (limit best : Nat) (previous : Best limit best) :
    Best (limit + 1) (visit best (limit + 1)) := by
  by_cases accepted : eligible (limit + 1)
  · rw [visit_new limit best previous accepted]
    by_cases zero : best = 0
    · rw [if_pos zero]
      have only (n : Nat) (bound : n ≤ limit + 1) (eligibleN : eligible n) : n = limit + 1 := by
        by_contra different
        exact previous.empty zero n (by omega) eligibleN
      refine ⟨fun _ => ⟨accepted, le_rfl⟩, ?_, ?_, ?_⟩
      · intro impossible
        omega
      · intro _ n bound eligibleN
        rw [only n bound eligibleN]
      · intro _ n bound eligibleN _
        rw [only n bound eligibleN]
    · rw [if_neg zero]
      by_cases improved : ratio (limit + 1) < ratio best
      · rw [if_pos improved]
        refine ⟨fun _ => ⟨accepted, le_rfl⟩, ?_, ?_, ?_⟩
        · intro impossible
          omega
        · intro _ n bound eligibleN
          by_cases last : n = limit + 1
          · subst n; exact le_rfl
          · exact improved.le.trans (previous.minimizes zero n (by omega) eligibleN)
        · intro _ n bound eligibleN same
          by_cases last : n = limit + 1
          · omega
          · have old := previous.minimizes zero n (by omega) eligibleN
            rw [← same] at old
            exact False.elim ((not_lt_of_ge old) improved)
      · rw [if_neg improved]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro nonzero
          obtain ⟨chosen, bound⟩ := previous.selected nonzero
          exact ⟨chosen, by omega⟩
        · intro impossible
          exact False.elim (zero impossible)
        · intro nonzero n bound eligibleN
          by_cases last : n = limit + 1
          · subst n; exact le_of_not_gt improved
          · exact previous.minimizes nonzero n (by omega) eligibleN
        · intro nonzero n bound eligibleN same
          by_cases last : n = limit + 1
          · have oldBound := (previous.selected nonzero).2
            omega
          · exact previous.least nonzero n (by omega) eligibleN same
  · rw [visit, if_neg accepted]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro nonzero
      obtain ⟨chosen, bound⟩ := previous.selected nonzero
      exact ⟨chosen, by omega⟩
    · intro zero n bound eligibleN
      by_cases last : n = limit + 1
      · subst n; exact accepted eligibleN
      · exact previous.empty zero n (by omega) eligibleN
    · intro nonzero n bound eligibleN
      by_cases last : n = limit + 1
      · subst n; exact False.elim (accepted eligibleN)
      · exact previous.minimizes nonzero n (by omega) eligibleN
    · intro nonzero n bound eligibleN same
      by_cases last : n = limit + 1
      · subst n; exact False.elim (accepted eligibleN)
      · exact previous.least nonzero n (by omega) eligibleN same

theorem bestUpTo_spec (limit : Nat) : Best limit (bestUpTo limit) := by
  induction limit with
  | zero =>
      refine ⟨fun impossible => False.elim (impossible rfl), ?_,
        fun impossible => False.elim (impossible rfl),
        fun impossible => False.elim (impossible rfl)⟩
      intro _ n bound eligibleN
      have large := eligibleN.1
      omega
  | succ limit ih => exact best_step limit (bestUpTo limit) ih

theorem fold_range_best (limit : Nat) :
    (List.range (limit + 1)).foldl visit 0 = bestUpTo limit := by
  induction limit with
  | zero => exact visit_zero 0
  | succ limit ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih, bestUpTo]

/-- Negative bounds and empty candidate ranges have the same zero result. -/
theorem signed_fold (limit : Int) :
    (List.range (limit + 1).toNat).foldl visit 0 = result limit := by
  by_cases negative : limit < 0
  · have empty : (limit + 1).toNat = 0 := by omega
    have clipped : limit.toNat = 0 := by omega
    simp only [empty, List.range_zero, List.foldl_nil, result, clipped, bestUpTo]
  · have count : (limit + 1).toNat = limit.toNat + 1 := by omega
    rw [count, fold_range_best]
    rfl

theorem best_unique (limit a b : Nat) (left : Best limit a) (right : Best limit b) : a = b := by
  by_cases zeroA : a = 0
  · by_cases zeroB : b = 0
    · omega
    · exact False.elim (left.empty zeroA b (right.selected zeroB).2 (right.selected zeroB).1)
  · by_cases zeroB : b = 0
    · exact False.elim (right.empty zeroB a (left.selected zeroA).2 (left.selected zeroA).1)
    · have aChosen := left.selected zeroA
      have bChosen := right.selected zeroB
      have same : ratio a = ratio b := le_antisymm
        (left.minimizes zeroA b bChosen.2 bChosen.1)
        (right.minimizes zeroB a aChosen.2 aChosen.1)
      exact Nat.le_antisymm (left.least zeroA b bChosen.2 bChosen.1 same)
        (right.least zeroB a aChosen.2 aChosen.1 same.symm)

end ProjectEulerStatements.TotientPermutation
