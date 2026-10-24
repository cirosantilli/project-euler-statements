import ProjectEulerStatements.P30
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Range
import Mathlib.Tactic.NormNum

/-! The six fifth-power digit sums, checked through sorted digit multisets.

Every number below one million has six decimal digits after zero padding.
Sorting those digits preserves their fifth-power sum and reduces the finite
certificate to 5,005 multisets, split into ten independent rows. -/
namespace ProjectEulerStatements.FifthPowerDigits
open P30

def solutions : List Nat := [4150, 4151, 54748, 92727, 93084, 194979]

private def digitSum (digits : List Nat) : Nat := (digits.map (fun d => d ^ 5)).sum

/-- Nondecreasing digit lists of a prescribed length and minimum digit. -/
private def selections : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | count + 1, lower => (List.range' lower (10 - lower)).flatMap fun digit =>
      (selections count digit).map (digit :: ·)

private theorem mem_selections (count lower : Nat) (digits : List Nat)
    (length : digits.length = count) (ordered : digits.Pairwise (· ≤ ·))
    (bounds : ∀ digit ∈ digits, lower ≤ digit ∧ digit < 10) :
    digits ∈ selections count lower := by
  induction count generalizing lower digits with
  | zero =>
      have empty : digits = [] := List.length_eq_zero_iff.mp length
      simp [empty, selections]
  | succ count ih =>
      cases digits with
      | nil => simp at length
      | cons digit tail =>
          have headBounds := bounds digit (by simp)
          have order := List.pairwise_cons.mp ordered
          apply List.mem_flatMap.mpr
          refine ⟨digit, ?_, List.mem_map.mpr ⟨tail, ?_, rfl⟩⟩
          · apply List.mem_range'.mpr
            exact ⟨digit - lower, by omega, by omega⟩
          · exact ih digit tail (by simpa using length) order.2
              (fun d member => ⟨order.1 d member, (bounds d (by simp [member])).2⟩)

private theorem padded_sum (n : Nat) : digitSum (Nat.digitsAppend 10 6 n) = digitPowerSum 5 n := by
  simp [digitSum, Nat.digitsAppend, digitPowerSum, foldl_add_eq_sum]

private def good (n : Nat) : Bool := decide (2 ≤ n ∧ digitPowerSum 5 n = n)
private def checkedRow (digit : Nat) : List Nat :=
  ((selections 5 digit).map (fun tail => digitSum (digit :: tail))).filter good

set_option maxRecDepth 10000
set_option Elab.async false

-- Each reduction sees at most 2,002 multisets; the final combination reuses
-- these proof constants instead of evaluating the entire search again.
private theorem row0 : checkedRow 0 = [4150, 4151, 93084, 92727, 54748] := by decide +kernel
private theorem row1 : checkedRow 1 = [194979] := by decide +kernel
private theorem row2 : checkedRow 2 = [] := by decide +kernel
private theorem row3 : checkedRow 3 = [] := by decide +kernel
private theorem row4 : checkedRow 4 = [] := by decide +kernel
private theorem row5 : checkedRow 5 = [] := by decide +kernel
private theorem row6 : checkedRow 6 = [] := by decide +kernel
private theorem row7 : checkedRow 7 = [] := by decide +kernel
private theorem row8 : checkedRow 8 = [] := by decide +kernel
private theorem row9 : checkedRow 9 = [] := by decide +kernel

private theorem rows_checked : (List.range 10).flatMap checkedRow =
    [4150, 4151, 93084, 92727, 54748, 194979] := by
  change checkedRow 0 ++ (checkedRow 1 ++ (checkedRow 2 ++ (checkedRow 3 ++
    (checkedRow 4 ++ (checkedRow 5 ++ (checkedRow 6 ++ (checkedRow 7 ++
    (checkedRow 8 ++ (checkedRow 9 ++ []))))))))) = _
  rw [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9]
  rfl

private theorem member_checked (n : Nat) (small : n < 1000000)
    (lower : 2 ≤ n) (fixed : digitPowerSum 5 n = n) :
    n ∈ (List.range 10).flatMap checkedRow := by
  let padded := Nat.digitsAppend 10 6 n
  let sorted := padded.mergeSort (· ≤ ·)
  have permutation : sorted.Perm padded := List.mergeSort_perm _ _
  have length : sorted.length = 6 := by
    rw [permutation.length_eq]
    exact Nat.length_digitsAppend (by decide) 6 (by simpa using small)
  have order : sorted.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) padded
  have bounds : ∀ digit ∈ sorted, 0 ≤ digit ∧ digit < 10 := by
    intro digit member
    exact ⟨Nat.zero_le _, Nat.lt_of_mem_digitsAppend (by decide) 6 digit (permutation.mem_iff.mp member)⟩
  have selected := mem_selections 6 0 sorted length order bounds
  have sum : digitSum sorted = n := by
    exact ((permutation.map (fun d => d ^ 5)).sum_nat).trans ((padded_sum n).trans fixed)
  change sorted ∈ (List.range' 0 10).flatMap
    (fun digit => (selections 5 digit).map (digit :: ·)) at selected
  obtain ⟨digit, digitMember, tailMember⟩ := List.mem_flatMap.mp selected
  obtain ⟨tail, selectedTail, equal⟩ := List.mem_map.mp tailMember
  apply List.mem_flatMap.mpr
  refine ⟨digit, by simpa only [List.range_eq_range'] using digitMember, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨tail, selectedTail, ?_⟩, ?_⟩
  · exact (congrArg digitSum equal).trans sum
  · simpa [good] using And.intro lower fixed

theorem matches_bounds (n : Nat) (member : n ∈ solutions) : 2 ≤ n ∧ n ≤ 354294 := by
  simp only [solutions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem matches_fixed : ∀ n ∈ solutions, digitPowerSum 5 n = n := by decide +kernel

/-- Completeness of the finite certificate on the whole six-digit domain. -/
theorem fixed_iff (n : Nat) (small : n < 1000000) :
    (2 ≤ n ∧ digitPowerSum 5 n = n) ↔ n ∈ solutions := by
  constructor
  · rintro ⟨lower, fixed⟩
    have member := member_checked n small lower fixed
    rw [rows_checked] at member
    simpa only [solutions, List.mem_cons, List.mem_singleton, or_assoc, or_left_comm, or_comm] using member
  · intro member
    exact ⟨(matches_bounds n member).1, matches_fixed n member⟩

/-- The ordered source scan has precisely the six asserted solutions. -/
theorem optimized_matches :
    (List.range' 2 354293).filter (fun n => decide (digitPowerSum 5 n = n)) = solutions := by
  apply List.Pairwise.eq_of_mem_iff ((List.pairwise_lt_range' (s := 2) (n := 354293)).filter _)
    (by decide : solutions.Pairwise (· < ·))
  intro n
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨member, fixed⟩
    obtain ⟨i, bound, rfl⟩ := List.mem_range'.mp member
    exact (fixed_iff _ (by omega)).mp ⟨by omega, fixed⟩
  · intro member
    obtain ⟨lower, upper⟩ := matches_bounds n member
    exact ⟨List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩, matches_fixed n member⟩

/-- The reference's slightly larger bound adds no nonzero fixed point. -/
theorem no_extra (n : Nat) (large : 354294 < n) (bound : n ≤ limit 5) :
    digitPowerSum 5 n ≠ n := by
  intro fixed
  have member := (fixed_iff n (by norm_num [limit] at bound; omega)).mp ⟨by omega, fixed⟩
  have upper := (matches_bounds n member).2
  omega

private theorem reference_matches :
    (List.range (limit 5 + 1)).filter (fun n => decide (n ≠ 1 ∧ digitPowerSum 5 n = n)) =
      0 :: solutions := by
  apply List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _)
    (by decide : (0 :: solutions).Pairwise (· < ·))
  intro n
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨bound, notOne, fixed⟩
    by_cases zero : n = 0
    · exact Or.inl zero
    · exact Or.inr ((fixed_iff n (by norm_num [limit] at bound; omega)).mp ⟨by omega, fixed⟩)
  · rintro (rfl | member)
    · norm_num [limit, digitPowerSum]
    · obtain ⟨lower, upper⟩ := matches_bounds n member
      exact ⟨by norm_num [limit]; omega, by omega, matches_fixed n member⟩

private theorem fold_filter (p initial : Nat) (items : List Nat) :
    items.foldl (fun total n => if n = 1 then total
      else if digitPowerSum p n = n then total + n else total) initial =
      initial + (items.filter (fun n => decide (n ≠ 1 ∧ digitPowerSum p n = n))).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      by_cases one : head = 1 <;> by_cases fixed : digitPowerSum p head = head <;>
        simp [List.foldl_cons, one, fixed, ih, Nat.add_assoc]

theorem reference_value : P30.naive 5 = 443839 := by
  unfold P30.naive sumPowerDigits
  rw [fold_filter, reference_matches]
  decide

theorem matches_sum : solutions.sum = 443839 := by decide

end ProjectEulerStatements.FifthPowerDigits
