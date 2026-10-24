import ProjectEulerStatements.Lib.DoublePalindromes
import Mathlib.Data.List.Palindrome

/-! Decimal mirror construction, normalization, and recovery of the half-seed.
All digits remain symbolic; no search interval is evaluated. -/
namespace ProjectEulerStatements.DoublePalindromes

set_option Elab.async false

def DecimalWord (digits : List Nat) : Prop :=
  digits ≠ [] ∧ (∀ digit ∈ digits, digit < 10) ∧
    ∀ nonempty : digits ≠ [], digits.head nonempty ≠ 0

theorem decimalDigits_word (seed : Nat) (positive : 0 < seed) :
    DecimalWord (decimalDigits seed) := by
  have nonempty : Nat.digits 10 seed ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (show seed ≠ 0 by omega)
  refine ⟨by simpa [decimalDigits] using nonempty, ?_, ?_⟩
  · intro digit member
    exact Nat.digits_lt_base (by decide : 1 < 10)
      (List.mem_reverse.mp member)
  · intro present
    simpa [decimalDigits] using Nat.getLast_digit_ne_zero 10 (show seed ≠ 0 by omega)

theorem decimalDigits_value (digits : List Nat) (word : DecimalWord digits) :
    decimalDigits (Nat.ofDigits 10 digits.reverse) = digits := by
  unfold decimalDigits
  rw [Nat.digits_ofDigits 10 (by decide) _
    (fun digit member => word.2.1 digit (List.mem_reverse.mp member))]
  · exact List.reverse_reverse digits
  · intro nonempty
    simpa only [List.getLast_reverse] using word.2.2 word.1

theorem value_positive (digits : List Nat) (word : DecimalWord digits) :
    0 < Nat.ofDigits 10 digits.reverse := by
  have recovered := decimalDigits_value digits word
  by_contra notPositive
  have zero : Nat.ofDigits 10 digits.reverse = 0 := by omega
  rw [zero] at recovered
  exact word.1 (by simpa [decimalDigits] using recovered.symm)

theorem decimalWord_append (digits tail : List Nat) (word : DecimalWord digits)
    (bounds : ∀ digit ∈ tail, digit < 10) : DecimalWord (digits ++ tail) := by
  refine ⟨by simp [word.1], ?_, ?_⟩
  · intro digit member
    rcases List.mem_append.mp member with first | second
    · exact word.2.1 digit first
    · exact bounds digit second
  · intro nonempty
    simpa only [List.head_append_left word.1] using word.2.2 word.1

theorem oddDigits_word (seed : Nat) (positive : 0 < seed) : DecimalWord (oddDigits seed) := by
  have word := decimalDigits_word seed positive
  apply decimalWord_append _ _ word
  intro digit member
  exact word.2.1 digit (List.dropLast_subset _ (List.mem_reverse.mp member))

theorem evenDigits_word (seed : Nat) (positive : 0 < seed) :
    DecimalWord (evenDigits seed) := by
  have word := decimalDigits_word seed positive
  exact decimalWord_append _ _ word
    (fun digit member => word.2.1 digit (List.mem_reverse.mp member))

theorem decimalDigits_oddPalindrome (seed : Nat) (positive : 0 < seed) :
    decimalDigits (oddPalindrome seed) = oddDigits seed :=
  decimalDigits_value _ (oddDigits_word seed positive)

theorem decimalDigits_evenPalindrome (seed : Nat) (positive : 0 < seed) :
    decimalDigits (evenPalindrome seed) = evenDigits seed :=
  decimalDigits_value _ (evenDigits_word seed positive)

theorem oddPalindrome_positive (seed : Nat) (positive : 0 < seed) :
    0 < oddPalindrome seed := value_positive _ (oddDigits_word seed positive)

theorem evenPalindrome_positive (seed : Nat) (positive : 0 < seed) :
    0 < evenPalindrome seed := value_positive _ (evenDigits_word seed positive)

theorem odd_mirror_palindrome (digits : List Nat) :
    (digits ++ digits.dropLast.reverse).Palindrome := by
  induction digits with
  | nil => exact .nil
  | cons head tail ih =>
      cases tail with
      | nil => exact .singleton head
      | cons next rest =>
          simpa [List.dropLast_cons_of_ne_nil, List.append_assoc] using
            List.Palindrome.cons_concat head ih

theorem oddPalindrome_palindrome (seed : Nat) (positive : 0 < seed) :
    P36.isPalindromeBase 10 (oddPalindrome seed) = true := by
  have mirrored := (odd_mirror_palindrome (decimalDigits seed)).reverse_eq
  have recovered := decimalDigits_oddPalindrome seed positive
  have digits : Nat.digits 10 (oddPalindrome seed) = (oddDigits seed).reverse := by
    simpa [decimalDigits] using congrArg List.reverse recovered
  simp only [P36.isPalindromeBase, digits, List.reverse_reverse]
  exact decide_eq_true (by simpa only [oddDigits] using mirrored)

theorem evenPalindrome_palindrome (seed : Nat) (positive : 0 < seed) :
    P36.isPalindromeBase 10 (evenPalindrome seed) = true := by
  have mirrored := (List.Palindrome.append_reverse (decimalDigits seed)).reverse_eq
  have recovered := decimalDigits_evenPalindrome seed positive
  have digits : Nat.digits 10 (evenPalindrome seed) = (evenDigits seed).reverse := by
    simpa [decimalDigits] using congrArg List.reverse recovered
  simp only [P36.isPalindromeBase, digits, List.reverse_reverse]
  exact decide_eq_true (by simpa only [evenDigits] using mirrored)

/-- Every palindrome is the even mirror of a half, or the odd mirror of a
nonempty half. The induction adds a matching digit at each end. -/
theorem palindrome_half {digits : List Nat} (palindrome : digits.Palindrome) :
    ∃ half, digits = half ++ half.reverse ∨
      (half ≠ [] ∧ digits = half ++ half.dropLast.reverse) := by
  induction palindrome with
  | nil => exact ⟨[], Or.inl rfl⟩
  | singleton digit => exact ⟨[digit], Or.inr ⟨by simp, rfl⟩⟩
  | cons_concat digit palindrome ih =>
      obtain ⟨half, even | ⟨nonempty, odd⟩⟩ := ih
      · refine ⟨digit :: half, Or.inl ?_⟩
        simp [even, List.append_assoc]
      · refine ⟨digit :: half, Or.inr ⟨by simp, ?_⟩⟩
        simp [odd, List.dropLast_cons_of_ne_nil nonempty, List.append_assoc]

end ProjectEulerStatements.DoublePalindromes
