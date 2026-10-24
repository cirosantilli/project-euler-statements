import ProjectEulerStatements.Lib.DoublePalindromeMirrors
import Mathlib.Data.List.Nodup

/-! Completeness and uniqueness of the decimal mirror enumeration. The bound
on the seed follows from the length of a symbolic palindrome. -/
namespace ProjectEulerStatements.DoublePalindromes

set_option Elab.async false

@[simp] theorem value_decimalDigits (n : Nat) :
    Nat.ofDigits 10 (decimalDigits n).reverse = n := by
  simp [decimalDigits, Nat.ofDigits_digits]

theorem decimalDigits_injective : Function.Injective decimalDigits := by
  intro left right equal
  calc
    left = Nat.ofDigits 10 (decimalDigits left).reverse := (value_decimalDigits left).symm
    _ = Nat.ofDigits 10 (decimalDigits right).reverse :=
      congrArg (fun digits => Nat.ofDigits 10 digits.reverse) equal
    _ = right := value_decimalDigits right

theorem decimalWord_prefix (half tail : List Nat) (word : DecimalWord (half ++ tail))
    (nonempty : half ≠ []) : DecimalWord half := by
  refine ⟨nonempty, ?_, ?_⟩
  · intro digit member
    exact word.2.1 digit (List.mem_append_left _ member)
  · intro present
    simpa only [List.head_append_left present] using word.2.2 word.1

theorem seed_of_half (half : List Nat) (word : DecimalWord half) (short : half.length ≤ 3) :
    ∃ seed, 0 < seed ∧ seed < 1000 ∧ decimalDigits seed = half := by
  let seed := Nat.ofDigits 10 half.reverse
  have bound : seed < 10 ^ half.length := by
    simpa [seed] using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10)
      (fun digit member => word.2.1 digit (List.mem_reverse.mp member))
  have power : 10 ^ half.length ≤ 1000 :=
    Nat.pow_le_pow_right (by decide) short
  exact ⟨seed, value_positive half word, Nat.lt_of_lt_of_le bound power,
    decimalDigits_value half word⟩

theorem palindrome_seed (n : Nat) (positive : 0 < n) (bound : n < 1000000)
    (palindrome : P36.isPalindromeBase 10 n = true) :
    ∃ seed, 0 < seed ∧ seed < 1000 ∧
      (oddPalindrome seed = n ∨ evenPalindrome seed = n) := by
  have word := decimalDigits_word n positive
  have reversed : (Nat.digits 10 n).reverse = Nat.digits 10 n :=
    (of_decide_eq_true palindrome).symm
  have pal : (decimalDigits n).Palindrome := by
    apply List.Palindrome.of_reverse_eq
    simpa [decimalDigits] using reversed.symm
  have short : (decimalDigits n).length ≤ 6 := by
    have bound' : n < 10 ^ 6 := bound
    simpa [decimalDigits] using
      (Nat.digits_length_le_iff (b := 10) (k := 6) (by decide) n).mpr bound'
  obtain ⟨half, even | ⟨nonempty, odd⟩⟩ := palindrome_half pal
  · have nonempty : half ≠ [] := by
      intro empty
      exact word.1 (by simpa [empty] using even)
    have halfWord := decimalWord_prefix half half.reverse (even ▸ word) nonempty
    have halfShort : half.length ≤ 3 := by
      rw [even, List.length_append, List.length_reverse] at short
      omega
    obtain ⟨seed, seedPositive, seedBound, recovered⟩ := seed_of_half half halfWord halfShort
    refine ⟨seed, seedPositive, seedBound, Or.inr ?_⟩
    simp only [evenPalindrome, evenDigits, recovered, ← even, value_decimalDigits]
  · have halfWord := decimalWord_prefix half half.dropLast.reverse (odd ▸ word) nonempty
    have halfShort : half.length ≤ 3 := by
      rw [odd, List.length_append, List.length_reverse, List.length_dropLast] at short
      omega
    obtain ⟨seed, seedPositive, seedBound, recovered⟩ := seed_of_half half halfWord halfShort
    refine ⟨seed, seedPositive, seedBound, Or.inl ?_⟩
    simp only [oddPalindrome, oddDigits, recovered, ← odd, value_decimalDigits]

theorem odd_even_distinct (left right : Nat) (leftPositive : 0 < left)
    (rightPositive : 0 < right) : oddPalindrome left ≠ evenPalindrome right := by
  intro equal
  have digits := congrArg decimalDigits equal
  rw [decimalDigits_oddPalindrome left leftPositive,
    decimalDigits_evenPalindrome right rightPositive] at digits
  have lengths := congrArg List.length digits
  have nonempty := List.length_pos_of_ne_nil (decimalDigits_word left leftPositive).1
  simp only [oddDigits, evenDigits, List.length_append, List.length_reverse,
    List.length_dropLast] at lengths
  omega

theorem oddPalindrome_injective (left right : Nat) (leftPositive : 0 < left)
    (rightPositive : 0 < right) (equal : oddPalindrome left = oddPalindrome right) :
    left = right := by
  have digits := congrArg decimalDigits equal
  rw [decimalDigits_oddPalindrome left leftPositive,
    decimalDigits_oddPalindrome right rightPositive] at digits
  have lengths := congrArg List.length digits
  have leftLength := List.length_pos_of_ne_nil (decimalDigits_word left leftPositive).1
  have rightLength := List.length_pos_of_ne_nil (decimalDigits_word right rightPositive).1
  simp only [oddDigits, List.length_append, List.length_reverse, List.length_dropLast] at lengths
  have sameLength : (decimalDigits left).length = (decimalDigits right).length := by omega
  apply decimalDigits_injective
  have half := congrArg (List.take (decimalDigits left).length) digits
  simp only [oddDigits, List.take_left] at half
  rw [sameLength, List.take_left] at half
  exact half

theorem evenPalindrome_injective (left right : Nat) (leftPositive : 0 < left)
    (rightPositive : 0 < right) (equal : evenPalindrome left = evenPalindrome right) :
    left = right := by
  have digits := congrArg decimalDigits equal
  rw [decimalDigits_evenPalindrome left leftPositive,
    decimalDigits_evenPalindrome right rightPositive] at digits
  have lengths := congrArg List.length digits
  simp only [evenDigits, List.length_append, List.length_reverse] at lengths
  have sameLength : (decimalDigits left).length = (decimalDigits right).length := by omega
  apply decimalDigits_injective
  have half := congrArg (List.take (decimalDigits left).length) digits
  simp only [evenDigits, List.take_left] at half
  rw [sameLength, List.take_left] at half
  exact half

theorem mem_candidates (n : Nat) : n ∈ candidates ↔
    ∃ seed, 0 < seed ∧ seed < 1000 ∧
      (oddPalindrome seed = n ∨ evenPalindrome seed = n) := by
  simp only [candidates, List.mem_flatMap, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨seed, ⟨lower, upper⟩, odd | even⟩
    · exact ⟨seed, by omega, by omega, Or.inl odd.symm⟩
    · exact ⟨seed, by omega, by omega, Or.inr even.symm⟩
  · rintro ⟨seed, lower, upper, odd | even⟩
    · exact ⟨seed, ⟨by omega, by omega⟩, Or.inl odd.symm⟩
    · exact ⟨seed, ⟨by omega, by omega⟩, Or.inr even.symm⟩

theorem candidate_positive (n : Nat) (member : n ∈ candidates) : 0 < n := by
  obtain ⟨seed, positive, _, rfl | rfl⟩ := (mem_candidates n).mp member
  · exact oddPalindrome_positive seed positive
  · exact evenPalindrome_positive seed positive

theorem candidate_palindrome (n : Nat) (member : n ∈ candidates) :
    P36.isPalindromeBase 10 n = true := by
  obtain ⟨seed, positive, _, rfl | rfl⟩ := (mem_candidates n).mp member
  · exact oddPalindrome_palindrome seed positive
  · exact evenPalindrome_palindrome seed positive

theorem candidates_nodup : candidates.Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro seed member
    have positive : 0 < seed := by have := List.mem_range'_1.mp member; omega
    simp [odd_even_distinct seed seed positive positive]
  · apply (List.nodup_range' (s := 1) (n := 999)).pairwise_of_forall_ne
    intro left leftMember right rightMember different
    have leftPositive : 0 < left := by have := List.mem_range'_1.mp leftMember; omega
    have rightPositive : 0 < right := by have := List.mem_range'_1.mp rightMember; omega
    apply List.disjoint_left.mpr
    intro value first second
    simp only [List.mem_cons, List.not_mem_nil, or_false] at first second
    rcases first with first | first <;> rcases second with second | second
    · exact different (oddPalindrome_injective left right leftPositive rightPositive
        (first.symm.trans second))
    · exact odd_even_distinct left right leftPositive rightPositive (first.symm.trans second)
    · exact odd_even_distinct right left rightPositive leftPositive (second.symm.trans first)
    · exact different (evenPalindrome_injective left right leftPositive rightPositive
        (first.symm.trans second))

theorem mem_generate (limit n : Nat) (bound : limit ≤ 1000000) :
    n ∈ generate limit ↔ 0 < n ∧ n < limit ∧ P36.isPalindromeBase 10 n = true := by
  constructor
  · intro member
    obtain ⟨candidate, inside⟩ := List.mem_filter.mp member
    exact ⟨candidate_positive n candidate, of_decide_eq_true inside,
      candidate_palindrome n candidate⟩
  · rintro ⟨positive, inside, palindrome⟩
    exact List.mem_filter.mpr ⟨(mem_candidates n).mpr
      (palindrome_seed n positive (by omega) palindrome), decide_eq_true inside⟩

theorem generate_nodup (limit : Nat) : (generate limit).Nodup :=
  candidates_nodup.filter _

end ProjectEulerStatements.DoublePalindromes
