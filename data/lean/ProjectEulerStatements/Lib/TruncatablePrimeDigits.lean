import ProjectEulerStatements.Lib.TruncatablePrimeBase

/-! Digit-list truncations and arithmetic truncations express the same conditions.
Suffixes with leading zero digits retain their ordinary positional value. -/
namespace ProjectEulerStatements.TruncatablePrimeBase

set_option Elab.async false

def digitsBE (base n : Nat) : List Nat := (Nat.digits base n).reverse
def ofDigitsBE (base : Nat) (digits : List Nat) : Nat := Nat.ofDigits base digits.reverse

def truncations (base n : Nat) : List Nat :=
  let digits := digitsBE base n
  let width := digits.length
  (List.range (width - 1)).map (fun i => ofDigitsBE base (digits.drop (i + 1))) ++
    (List.range (width - 1)).map (fun i => ofDigitsBE base (digits.take (width - i - 1)))

def digitCheck (base n : Nat) : Bool :=
  (truncations base n).all fun part => decide (Nat.Prime part)

theorem ofDigitsBE_take (base n count : Nat) (valid : 2 ≤ base) :
    ofDigitsBE base ((digitsBE base n).take count) =
      n / base ^ ((digitsBE base n).length - count) := by
  simp only [ofDigitsBE, digitsBE, List.reverse_take, List.reverse_reverse, List.length_reverse]
  exact (Nat.self_div_pow_eq_ofDigits_drop _ n valid).symm

theorem ofDigitsBE_drop (base n count : Nat) (valid : 2 ≤ base) :
    ofDigitsBE base ((digitsBE base n).drop count) =
      n % base ^ ((digitsBE base n).length - count) := by
  simp only [ofDigitsBE, digitsBE, List.reverse_drop, List.reverse_reverse, List.length_reverse]
  exact (Nat.self_mod_pow_eq_ofDigits_take _ n valid).symm

theorem digitCheck_iff (base n : Nat) (valid : 2 ≤ base) :
    digitCheck base n = true ↔
      (∀ count, 0 < count → count < (Nat.digits base n).length →
        Nat.Prime (n % base ^ count)) ∧
      (∀ count, 0 < count → count < (Nat.digits base n).length →
        Nat.Prime (n / base ^ count)) := by
  simp only [digitCheck, truncations, List.all_append, Bool.and_eq_true,
    List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq, List.mem_range,
    ofDigitsBE_drop base n _ valid, ofDigitsBE_take base n _ valid]
  simp only [digitsBE, List.length_reverse]
  constructor
  · rintro ⟨left, right⟩
    constructor
    · intro count positive inside
      have index : (Nat.digits base n).length - count - 1 < (Nat.digits base n).length - 1 := by
        omega
      have checked := left _ index
      have equal : (Nat.digits base n).length -
          ((Nat.digits base n).length - count - 1 + 1) = count := by omega
      simpa only [equal] using checked
    · intro count positive inside
      have index : count - 1 < (Nat.digits base n).length - 1 := by omega
      have checked := right _ index
      have equal : (Nat.digits base n).length -
          ((Nat.digits base n).length - (count - 1) - 1) = count := by omega
      simpa only [equal] using checked
  · rintro ⟨left, right⟩
    constructor
    · intro index inside
      exact left _ (by omega) (by omega)
    · intro index inside
      have equal : (Nat.digits base n).length -
          ((Nat.digits base n).length - index - 1) = index + 1 := by omega
      rw [equal]
      exact right (index + 1) (by omega) (by omega)

theorem rightPrime_iff (base n : Nat) (valid : 2 ≤ base) (positive : 0 < n) :
    RightPrime base n ↔ Nat.Prime n ∧
      ∀ count, 0 < count → count < (Nat.digits base n).length →
        Nat.Prime (n / base ^ count) := by
  constructor
  · intro right
    refine ⟨right_prime base n positive right, ?_⟩
    intro count _ inside
    have lower := (Nat.lt_digits_length_iff valid n).mp inside
    exact right count (Nat.div_pos lower (Nat.pow_pos (by omega : 0 < base)))
  · rintro ⟨prime, proper⟩ count remaining
    cases count with
    | zero => simpa using prime
    | succ count =>
        apply proper (count + 1) (by omega)
        apply (Nat.lt_digits_length_iff valid n).mpr
        exact (Nat.div_pos_iff.mp remaining).2

/-- On a generated prime, checking the proper left suffixes is sufficient. -/
theorem digitCheck_of_rightPrime (base n : Nat) (valid : 2 ≤ base) (positive : 0 < n)
    (right : RightPrime base n) : digitCheck base n = leftCheck base n := by
  apply Bool.eq_iff_iff.mpr
  rw [digitCheck_iff base n valid, leftCheck_iff base n valid]
  have checked := (rightPrime_iff base n valid positive).mp right
  constructor
  · rintro ⟨left, _⟩ count lower power
    exact left count lower ((Nat.lt_digits_length_iff valid n).mpr power)
  · intro left
    exact ⟨fun count lower inside =>
      left count lower ((Nat.lt_digits_length_iff valid n).mp inside), checked.2⟩

def referenceCheck (base n : Nat) : Bool :=
  decide (base ≤ n) && decide (Nat.Prime n) && digitCheck base n

theorem referenceCheck_iff (base n : Nat) (valid : 2 ≤ base) :
    referenceCheck base n = true ↔ Truncatable base n := by
  simp only [referenceCheck, Bool.and_eq_true, decide_eq_true_eq, Truncatable]
  constructor
  · rintro ⟨⟨large, prime⟩, digits⟩
    obtain ⟨left, right⟩ := (digitCheck_iff base n valid).mp digits
    refine ⟨large, (rightPrime_iff base n valid (by omega)).mpr ⟨prime, right⟩, ?_⟩
    intro count lower power
    exact left count lower ((Nat.lt_digits_length_iff valid n).mpr power)
  · rintro ⟨large, right, left⟩
    have prime := right_prime base n (by omega) right
    refine ⟨⟨large, prime⟩, ?_⟩
    rw [digitCheck_of_rightPrime base n valid (by omega) right, leftCheck_iff base n valid]
    exact left

end ProjectEulerStatements.TruncatablePrimeBase
