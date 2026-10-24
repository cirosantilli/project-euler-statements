import ProjectEulerStatements.P34
import Init.Data.List.Nat.Range
import Lean.Elab.Tactic.Omega

/-! Shared mathematical interfaces for the reference and table-based digit
factorial searches. No reduction enumerates the full search interval. -/
namespace ProjectEulerStatements.DigitFactorial

set_option Elab.async false

theorem fold_factorials (digits : List Nat) (initial : Nat) :
    digits.foldl (fun total digit => total + Nat.factorial digit) initial =
      initial + (digits.map Nat.factorial).sum := by
  induction digits generalizing initial with
  | nil => simp
  | cons digit rest ih => simp [List.foldl, ih, Nat.add_assoc]

theorem digitFactSum_eq_sum (n : Nat) :
    P34.digitFactSum n = ((Nat.digits 10 n).map Nat.factorial).sum := by
  simp [P34.digitFactSum, fold_factorials]

@[simp] theorem digitFactSum_zero : P34.digitFactSum 0 = 0 := by
  simp [P34.digitFactSum]

theorem digitFactSum_step (n : Nat) (positive : 0 < n) :
    P34.digitFactSum n = Nat.factorial (n % 10) + P34.digitFactSum (n / 10) := by
  rw [digitFactSum_eq_sum, Nat.digits_def' (by decide) positive,
    List.map_cons, List.sum_cons, ← digitFactSum_eq_sum]

def facts : List Nat := (List.range 10).map Nat.factorial

@[simp] theorem facts_length : facts.length = 10 := by simp [facts]

theorem facts_get (digit : Nat) (bound : digit < 10) :
    facts[digit]? = some (Nat.factorial digit) := by
  simp [facts, List.getElem?_range bound]

theorem facts_index (digit : Nat) (bound : digit < 10) :
    facts[digit]'(by simpa using bound) = Nat.factorial digit := by
  simp [facts]

theorem facts_values : facts = [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880] := by
  decide +kernel

theorem facts_nine : facts[9]? = some 362880 := by decide +kernel

/-- The reference predicate includes zero, whose contribution is zero. -/
def curious (n : Nat) : Bool := decide (n ≠ 1 ∧ n ≠ 2 ∧ P34.digitFactSum n = n)

private theorem reference_fold (items : List Nat) (initial : Nat) :
    items.foldl (fun total n => if n = 1 ∨ n = 2 then total
      else if P34.digitFactSum n = n then total + n else total) initial =
      initial + (items.filter curious).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head rest ih =>
      by_cases excluded : head = 1 ∨ head = 2
      · rcases excluded with rfl | rfl <;> simp [List.foldl, List.filter, curious, ih]
      · have notOne : head ≠ 1 := fun same => excluded (.inl same)
        have notTwo : head ≠ 2 := fun same => excluded (.inr same)
        by_cases fixed : P34.digitFactSum head = head <;>
          simp [List.foldl, List.filter, curious, notOne, notTwo, fixed, ih, Nat.add_assoc]

theorem naive_filter_sum (limit : Nat) :
    P34.naive limit = ((List.range (limit + 1)).filter curious).sum := by
  simp [P34.naive, P34.sumCurious, reference_fold]

private theorem omit_exclusions (items : List Nat) (initial : Nat)
    (large : ∀ n ∈ items, 3 ≤ n) :
    items.foldl (fun total n => if n = 1 ∨ n = 2 then total
      else if P34.digitFactSum n = n then total + n else total) initial =
    items.foldl (fun total n => if P34.digitFactSum n = n then total + n else total) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons head rest ih =>
      have bound := large head (by simp)
      have excluded : ¬ (head = 1 ∨ head = 2) := by omega
      simp only [List.foldl_cons, if_neg excluded]
      exact ih _ (fun n member => large n (by simp [member]))

/-- Optimized enumeration starts at three, excluding 1 and 2. Zero contributes
nothing to the reference sum, so both intervals have exactly the same result. -/
theorem naive_range3 (limit : Nat) (bound : 2 ≤ limit) :
    P34.naive limit = (List.range' 3 (limit - 2)).foldl
      (fun total n => if P34.digitFactSum n = n then total + n else total) 0 := by
  have interval : List.range (limit + 1) = 0 :: 1 :: 2 :: List.range' 3 (limit - 2) := by
    rw [List.range_eq_range', show limit + 1 = ((limit - 2) + 1) + 1 + 1 by omega]
    rfl
  rw [P34.naive, P34.sumCurious, interval]
  change (List.range' 3 (limit - 2)).foldl
      (fun total n => if n = 1 ∨ n = 2 then total
        else if P34.digitFactSum n = n then total + n else total) 0 = _
  apply omit_exclusions
  intro n member
  exact (List.mem_range'_1.mp member).1

theorem default_bound : 7 * Nat.factorial 9 = 2540160 := by decide +kernel

/-- Only the eight small loop guards are evaluated here. -/
theorem digit_bound_guards :
    (List.range' 1 7).all (fun n => decide (10 ^ (n - 1) ≤ n * Nat.factorial 9)) = true ∧
      ¬ (10 ^ (8 - 1) ≤ 8 * Nat.factorial 9) := by
  decide +kernel

end ProjectEulerStatements.DigitFactorial
