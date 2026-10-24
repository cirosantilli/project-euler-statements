import ProjectEulerStatements.P38
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-! The decimal pandigital mask, with duplicate detection proved by individual
bit membership. No enumeration of digit strings is used. -/
namespace ProjectEulerStatements.PandigitalMask

set_option Elab.async false

def encode : List Nat → Nat
  | [] => 0
  | digit :: rest => encode rest ||| 2 ^ digit

theorem testBit_encode (digits : List Nat) (index : Nat) :
    (encode digits).testBit index = decide (index ∈ digits) := by
  induction digits with
  | nil => simp [encode]
  | cons head tail ih =>
      simp [encode, Nat.testBit_two_pow, ih, eq_comm, Bool.or_comm]

theorem encode_eq_of_members {left right : List Nat}
    (members : ∀ digit, digit ∈ left ↔ digit ∈ right) : encode left = encode right := by
  apply Nat.eq_of_testBit_eq
  intro digit
  simp only [testBit_encode, members digit]

theorem and_power_zero_iff (mask digit : Nat) :
    mask &&& 2 ^ digit = 0 ↔ mask.testBit digit = false := by
  constructor
  · intro zero
    have bit := congrArg (fun value : Nat => value.testBit digit) zero
    simpa only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true,
      Nat.zero_testBit] using bit
  · intro absent
    apply Nat.eq_of_testBit_eq
    intro index
    by_cases same : digit = index
    · subst index
      simp [absent]
    · simp [Nat.testBit_and, same]

theorem overlap_iff (seen : List Nat) (digit : Nat) :
    encode seen &&& 2 ^ digit ≠ 0 ↔ digit ∈ seen := by
  rw [ne_eq, and_power_zero_iff, testBit_encode]
  simp

theorem encode_move (digit : Nat) (items seen : List Nat) :
    encode (items ++ digit :: seen) = encode ((digit :: items) ++ seen) := by
  apply encode_eq_of_members
  intro value
  simp only [List.mem_append, List.mem_cons]
  tauto

/-- The source tests zero, tests an occupied bit, then inserts that bit. -/
def scan : List Nat → Nat → Bool
  | [], mask => decide (mask = 1022)
  | digit :: rest, mask =>
      if digit = 0 then false
      else if mask &&& 2 ^ digit ≠ 0 then false
      else scan rest (mask ||| 2 ^ digit)

def check (digits : List Nat) : Bool := decide (digits.length = 9) && scan digits 0

theorem scan_success (items seen : List Nat) (distinct : seen.Nodup) :
    scan items (encode seen) = true ↔
      0 ∉ items ∧ (items ++ seen).Nodup ∧ encode (items ++ seen) = 1022 := by
  induction items generalizing seen with
  | nil => simp [scan, distinct]
  | cons head tail ih =>
      by_cases zero : head = 0
      · subst head
        simp [scan]
      · by_cases duplicate : head ∈ seen
        · have overlap := (overlap_iff seen head).mpr duplicate
          simp only [scan, if_neg zero, if_pos overlap, Bool.false_eq_true, false_iff]
          rintro ⟨_, nodup, _⟩
          exact (List.nodup_cons.mp nodup).1 (List.mem_append_right _ duplicate)
        · have noOverlap : ¬ encode seen &&& 2 ^ head ≠ 0 :=
            fun overlap => duplicate ((overlap_iff seen head).mp overlap)
          have nextDistinct : (head :: seen).Nodup := List.nodup_cons.mpr ⟨duplicate, distinct⟩
          have next := ih (head :: seen) nextDistinct
          change scan tail (encode seen ||| 2 ^ head) = true ↔ _ at next
          rw [scan, if_neg zero, if_neg noOverlap, next]
          have permutation : List.Perm (tail ++ head :: seen) ((head :: tail) ++ seen) :=
            List.perm_middle
          constructor
          · rintro ⟨noZero, nodup, full⟩
            refine ⟨by simpa [Ne.symm zero] using noZero, permutation.nodup nodup, ?_⟩
            exact (encode_move head tail seen).symm.trans full
          · rintro ⟨noZero, nodup, full⟩
            refine ⟨fun member => noZero (List.mem_cons_of_mem _ member),
              permutation.symm.nodup nodup, ?_⟩
            exact (encode_move head tail seen).trans full

theorem scan_empty_success (digits : List Nat) :
    scan digits 0 = true ↔ 0 ∉ digits ∧ digits.Nodup ∧ encode digits = 1022 := by
  simpa only [encode, List.append_nil] using scan_success digits [] (by simp)

theorem target_bits (index : Nat) :
    (1022 : Nat).testBit index = decide (1 ≤ index ∧ index ≤ 9) := by
  by_cases small : index < 10
  · interval_cases index <;> decide
  · have power : 2 ^ 10 ≤ 2 ^ index := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have bound : 1022 < 2 ^ index := by omega
    rw [Nat.testBit_lt_two_pow bound]
    simp [show ¬ (1 ≤ index ∧ index ≤ 9) by omega]

theorem encode_full (digits : List Nat) (length : digits.length = 9)
    (bounds : ∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 9) (distinct : digits.Nodup) :
    encode digits = 1022 := by
  have subset : digits.toFinset ⊆ Finset.Icc 1 9 := by
    intro digit member
    exact Finset.mem_Icc.mpr (bounds digit (List.mem_toFinset.mp member))
  have same : digits.toFinset = Finset.Icc 1 9 := by
    apply Finset.eq_of_subset_of_card_le subset
    rw [List.toFinset_card_of_nodup distinct, length]
    decide
  apply Nat.eq_of_testBit_eq
  intro digit
  rw [testBit_encode, target_bits]
  apply decide_eq_decide.mpr
  rw [← List.mem_toFinset, same, Finset.mem_Icc]

private theorem eraseDups_nodup (items : List Nat) : items.eraseDups.Nodup := by
  induction measure : items.length using Nat.strong_induction_on generalizing items with
  | h size ih =>
      cases items with
      | nil => simp
      | cons head tail =>
          rw [List.eraseDups_cons, List.nodup_cons]
          constructor
          · intro present
            have filtered := List.mem_filter.mp (List.mem_eraseDups.mp present)
            simpa using filtered.2
          · exact ih _ (by
                have := List.length_filter_le (fun n => !(n == head)) tail
                simp only [List.length_cons] at measure
                omega)
              (tail.filter (fun n => !(n == head))) rfl

theorem eraseDups_length_eq_iff (digits : List Nat) :
    digits.eraseDups.length = digits.length ↔ digits.Nodup := by
  have same : digits.eraseDups.toFinset = digits.toFinset := by ext digit; simp
  have card := List.toFinset_card_of_nodup (eraseDups_nodup digits)
  rw [same] at card
  rw [← card]
  exact Multiset.toFinset_card_eq_card_iff_nodup (m := (digits : Multiset Nat))

/-- On decimal digit inputs, the source mask test is precisely the reference
length, nonzero-digit, and duplicate-free specification. -/
theorem check_correct (digits : List Nat) (decimal : ∀ digit ∈ digits, digit < 10) :
    check digits = true ↔ digits.length = 9 ∧
      (∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 9) ∧ digits.eraseDups.length = 9 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, scan_empty_success]
  constructor
  · rintro ⟨length, noZero, distinct, _⟩
    refine ⟨length, ?_, ?_⟩
    · intro digit member
      have bound := decimal digit member
      have nonzero : digit ≠ 0 := fun equal => noZero (equal ▸ member)
      omega
    · rw [← length]
      exact (eraseDups_length_eq_iff digits).mpr distinct
  · rintro ⟨length, bounds, erased⟩
    have distinct := (eraseDups_length_eq_iff digits).mp (erased.trans length.symm)
    have noZero : 0 ∉ digits := by
      intro member
      have positive := (bounds 0 member).1
      omega
    exact ⟨length, noZero, distinct, encode_full digits length bounds distinct⟩

theorem allDigitsOneToNine_eq_true (digits : List Nat) :
    P38.allDigitsOneToNine digits = true ↔
      ∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 9 := by
  have fold (items : List Nat) (initial : Bool) :
      items.foldl (fun acc d => acc && decide (1 ≤ d ∧ d ≤ 9)) initial =
        (initial && items.all (fun d => decide (1 ≤ d ∧ d ≤ 9))) := by
    induction items generalizing initial with
    | nil => simp
    | cons head tail ih =>
        simp only [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]
  simp only [P38.allDigitsOneToNine, fold, Bool.true_and, List.all_eq_true,
    decide_eq_true_eq]

theorem check_eq_reference_digits (digits : List Nat)
    (decimal : ∀ digit ∈ digits, digit < 10) :
    check digits = (decide (digits.length = 9) && P38.allDigitsOneToNine digits &&
      decide (digits.eraseDups.length = 9)) := by
  apply Bool.eq_iff_iff.mpr
  rw [check_correct digits decimal]
  simp only [Bool.and_eq_true, decide_eq_true_eq, allDigitsOneToNine_eq_true, and_assoc]

theorem check_digitsBE (n : Nat) : check (P38.digitsBE n) = P38.isPandigital1to9 n := by
  apply check_eq_reference_digits
  intro digit member
  exact Nat.digits_lt_base (by decide : 1 < 10) (List.mem_reverse.mp member)

end ProjectEulerStatements.PandigitalMask
