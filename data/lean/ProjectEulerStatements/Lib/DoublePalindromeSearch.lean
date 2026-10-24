import ProjectEulerStatements.Lib.DoublePalindromeSum

/-! Unbounded decimal-prefix enumeration, with a stopping rule derived from the input. -/
namespace ProjectEulerStatements.DoublePalindromeSearch
open DoublePalindromes
set_option Elab.async false

theorem odd_bounds (seed : Nat) (positive : 0 < seed) :
    seed * 10 ^ ((decimalDigits seed).length - 1) ≤ oddPalindrome seed ∧
      oddPalindrome seed < (seed + 1) * 10 ^ ((decimalDigits seed).length - 1) := by
  have split : oddPalindrome seed = Nat.ofDigits 10 (decimalDigits seed).dropLast +
      10 ^ ((decimalDigits seed).length - 1) * seed := by
    simp [oddPalindrome, oddDigits, List.reverse_append, Nat.ofDigits_append, value_decimalDigits]
  have remainder : Nat.ofDigits 10 (decimalDigits seed).dropLast <
      10 ^ ((decimalDigits seed).length - 1) := by
    simpa only [List.length_dropLast] using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10)
      (fun digit member =>
        (decimalDigits_word seed positive).2.1 digit (List.dropLast_subset _ member))
  rw [split]
  constructor
  · rw [Nat.mul_comm seed]
    omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm seed]
    omega

theorem seed_le_odd (seed : Nat) (positive : 0 < seed) : seed ≤ oddPalindrome seed := by
  exact (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))).trans (odd_bounds seed positive).1

theorem odd_strict {left right : Nat} (positive : 0 < left) (ordered : left < right) :
    oddPalindrome left < oddPalindrome right := by
  have lengths : (decimalDigits left).length ≤ (decimalDigits right).length := by
    simpa only [decimalDigits, List.length_reverse] using
      Nat.le_length_digits_le 10 left right ordered.le
  have powers : 10 ^ ((decimalDigits left).length - 1) ≤ 10 ^ ((decimalDigits right).length - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact (odd_bounds left positive).2.trans_le
    ((Nat.mul_le_mul (by omega : left + 1 ≤ right) powers).trans (odd_bounds right (by omega)).1)

theorem odd_mono {left right : Nat} (positive : 0 < left) (ordered : left ≤ right) :
    oddPalindrome left ≤ oddPalindrome right := by
  rcases ordered.eq_or_lt with equal | smaller
  · simp [equal]
  · exact (odd_strict positive smaller).le

theorem odd_le_even (seed : Nat) (positive : 0 < seed) :
    oddPalindrome seed ≤ evenPalindrome seed := by
  by_contra reversed
  have ordered : evenPalindrome seed ≤ oddPalindrome seed := by omega
  have lengths := Nat.le_length_digits_le 10 (evenPalindrome seed) (oddPalindrome seed) ordered
  have before := decimalDigits_evenPalindrome seed positive
  have after := decimalDigits_oddPalindrome seed positive
  have sizes := congrArg List.length before
  have sizes' := congrArg List.length after
  have nonempty := List.length_pos_iff.mpr (decimalDigits_word seed positive).1
  simp only [decimalDigits, evenDigits, oddDigits, List.length_append, List.length_reverse,
    List.length_dropLast] at lengths sizes sizes' nonempty
  omega

theorem palindrome_seed (n : Nat) (positive : 0 < n)
    (palindrome : P36.isPalindromeBase 10 n = true) :
    ∃ seed, 0 < seed ∧ (oddPalindrome seed = n ∨ evenPalindrome seed = n) := by
  have word := decimalDigits_word n positive
  have reversed : (Nat.digits 10 n).reverse = Nat.digits 10 n := (of_decide_eq_true palindrome).symm
  have pal : (decimalDigits n).Palindrome := by
    apply List.Palindrome.of_reverse_eq
    simpa [decimalDigits] using reversed.symm
  obtain ⟨half, even | ⟨nonempty, odd⟩⟩ := palindrome_half pal
  · have nonempty : half ≠ [] := by
      intro empty
      exact word.1 (by simpa [empty] using even)
    have halfWord := decimalWord_prefix half half.reverse (even ▸ word) nonempty
    let seed := Nat.ofDigits 10 half.reverse
    have recovered : decimalDigits seed = half := decimalDigits_value half halfWord
    refine ⟨seed, value_positive half halfWord, Or.inr ?_⟩
    simp only [evenPalindrome, evenDigits, recovered, ← even, value_decimalDigits]
  · have halfWord := decimalWord_prefix half half.dropLast.reverse (odd ▸ word) nonempty
    let seed := Nat.ofDigits 10 half.reverse
    have recovered : decimalDigits seed = half := decimalDigits_value half halfWord
    refine ⟨seed, value_positive half halfWord, Or.inl ?_⟩
    simp only [oddPalindrome, oddDigits, recovered, ← odd, value_decimalDigits]

def row (limit seed : Nat) : List Nat :=
  [oddPalindrome seed, evenPalindrome seed].filter (fun n => decide (n < limit))

def generateFrom (limit seed : Nat) : List Nat :=
  if 0 < seed ∧ oddPalindrome seed < limit then
    row limit seed ++ generateFrom limit (seed + 1)
  else []
termination_by limit - seed
decreasing_by
  have guarded : 0 < seed ∧ oddPalindrome seed < limit := by assumption
  have lower := seed_le_odd seed guarded.1
  omega

theorem generateFrom_step (limit seed : Nat) (positive : 0 < seed) :
    generateFrom limit seed = if oddPalindrome seed < limit then
      row limit seed ++ generateFrom limit (seed + 1) else [] := by
  rw [generateFrom]
  simp only [positive, true_and]

theorem mem_row (limit seed n : Nat) : n ∈ row limit seed ↔
    (oddPalindrome seed = n ∨ evenPalindrome seed = n) ∧ n < limit := by
  simp only [row, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
  tauto

theorem mem_from (limit seed n : Nat) (positive : 0 < seed) : n ∈ generateFrom limit seed ↔
    ∃ otherSeed, seed ≤ otherSeed ∧
      (oddPalindrome otherSeed = n ∨ evenPalindrome otherSeed = n) ∧ n < limit := by
  rw [generateFrom_step limit seed positive]
  by_cases inside : oddPalindrome seed < limit
  · rw [if_pos inside, List.mem_append, mem_row, mem_from limit (seed + 1) n (by omega)]
    constructor
    · rintro (⟨same, bounded⟩ | ⟨otherSeed, later, same, bounded⟩)
      · exact ⟨seed, Nat.le_refl _, same, bounded⟩
      · exact ⟨otherSeed, by omega, same, bounded⟩
    · rintro ⟨otherSeed, after, same, bounded⟩
      by_cases equal : otherSeed = seed
      · exact Or.inl ⟨equal ▸ same, bounded⟩
      · exact Or.inr ⟨otherSeed, by omega, same, bounded⟩
  · rw [if_neg inside]
    constructor
    · simp
    · rintro ⟨otherSeed, after, odd | even, bounded⟩
      · have lower := odd_mono positive after
        omega
      · have lower := (odd_mono positive after).trans (odd_le_even otherSeed (by omega))
        omega
termination_by limit - seed
decreasing_by
  have lower := seed_le_odd seed positive
  omega

def candidatesFrom (first count : Nat) : List Nat :=
  (List.range' first count).flatMap (fun seed => [oddPalindrome seed, evenPalindrome seed])

theorem candidates_nodup (first count : Nat) (positive : 0 < first) :
    (candidatesFrom first count).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro seed member
    have lower := (List.mem_range'_1.mp member).1
    simp [odd_even_distinct seed seed (by omega) (by omega)]
  · apply (List.nodup_range' (s := first) (n := count)).pairwise_of_forall_ne
    intro left leftMember right rightMember different
    have leftPositive : 0 < left := by have bound := (List.mem_range'_1.mp leftMember).1; omega
    have rightPositive : 0 < right := by have bound := (List.mem_range'_1.mp rightMember).1; omega
    apply List.disjoint_left.mpr
    intro value first second
    simp only [List.mem_cons, List.not_mem_nil, or_false] at first second
    rcases first with first | first <;> rcases second with second | second
    · exact different
        (oddPalindrome_injective left right leftPositive rightPositive (first.symm.trans second))
    · exact odd_even_distinct left right leftPositive rightPositive (first.symm.trans second)
    · exact odd_even_distinct right left rightPositive leftPositive (second.symm.trans first)
    · exact different
        (evenPalindrome_injective left right leftPositive rightPositive (first.symm.trans second))

theorem from_sublist (limit seed : Nat) (positive : 0 < seed) :
    List.Sublist (generateFrom limit seed) (candidatesFrom seed (limit - seed)) := by
  rw [generateFrom_step limit seed positive]
  by_cases inside : oddPalindrome seed < limit
  · rw [if_pos inside]
    have lower := seed_le_odd seed positive
    have count : limit - seed = (limit - (seed + 1)) + 1 := by omega
    rw [count, candidatesFrom, List.range'_succ, List.flatMap_cons]
    exact (List.filter_sublist (p := fun n => decide (n < limit))).append
      (from_sublist limit (seed + 1) (by omega))
  · rw [if_neg inside]
    exact List.nil_sublist _
termination_by limit - seed
decreasing_by omega

def generate (limit : Nat) : List Nat := generateFrom limit 1

theorem generate_nodup (limit : Nat) : (generate limit).Nodup :=
  (from_sublist limit 1 (by decide)).nodup (candidates_nodup 1 (limit - 1) (by decide))

theorem mem_generate (limit n : Nat) : n ∈ generate limit ↔
    0 < n ∧ n < limit ∧ P36.isPalindromeBase 10 n = true := by
  rw [generate, mem_from limit 1 n (by decide)]
  constructor
  · rintro ⟨seed, lower, odd | even, bounded⟩
    · exact ⟨odd ▸ oddPalindrome_positive seed (by omega), bounded,
        odd ▸ oddPalindrome_palindrome seed (by omega)⟩
    · exact ⟨even ▸ evenPalindrome_positive seed (by omega), bounded,
        even ▸ evenPalindrome_palindrome seed (by omega)⟩
  · rintro ⟨positive, bounded, palindrome⟩
    obtain ⟨seed, seedPositive, same⟩ := palindrome_seed n positive palindrome
    exact ⟨seed, by omega, same, bounded⟩

theorem generate_binary_sum (limit : Nat) :
    ((generate limit).filter (P36.isPalindromeBase 2)).sum = P36.naive limit := by
  rw [naive_filter_sum, filter_sum_without_zero]
  have same : ((generate limit).filter (P36.isPalindromeBase 2)).toFinset =
      ((List.range limit).filter
        (fun n => decide (0 < n) && P36.isDoublePalindrome n)).toFinset := by
    ext n
    simp only [List.mem_toFinset, List.mem_filter, mem_generate, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, P36.isDoublePalindrome]
    tauto
  have left := List.sum_toFinset (fun n : Nat => n)
    ((generate_nodup limit).filter (P36.isPalindromeBase 2))
  have right := List.sum_toFinset (fun n : Nat => n)
    ((show (List.range limit).Nodup from List.nodup_range).filter
      (fun n => decide (0 < n) && P36.isDoublePalindrome n))
  simp only [List.map_id_fun'] at left right
  rw [same] at left
  exact left.symm.trans right

def scan (limit : Nat) : Nat := (generate limit).foldl scanStep 0

theorem scan_correct (limit : Nat) : scan limit = P36.naive limit := by
  have positive : ∀ n ∈ generate limit, 0 < n :=
    fun n member => (mem_generate limit n).mp member |>.1
  simpa only [scan, scan_filter_sum _ 0 positive, Nat.zero_add] using generate_binary_sum limit

end ProjectEulerStatements.DoublePalindromeSearch
