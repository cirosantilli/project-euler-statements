import ProjectEulerStatements.Lib.TruncatablePrimes

/-! Proper decimal truncations as division and remainder, with bounds that
justify every sieve lookup. Leading-zero suffixes are interpreted numerically. -/
namespace ProjectEulerStatements.TruncatablePrimes

set_option Elab.async false

theorem digitsToNat_take (n count : Nat) :
    P37.digitsToNat ((P37.digitsBE n).take count) =
      n / 10 ^ ((P37.digitsBE n).length - count) := by
  simp only [P37.digitsToNat, P37.digitsBE, List.reverse_take, List.reverse_reverse,
    List.length_reverse]
  exact (Nat.self_div_pow_eq_ofDigits_drop _ n (by decide : 2 ≤ 10)).symm

theorem digitsToNat_drop (n count : Nat) :
    P37.digitsToNat ((P37.digitsBE n).drop count) =
      n % 10 ^ ((P37.digitsBE n).length - count) := by
  simp only [P37.digitsToNat, P37.digitsBE, List.reverse_drop, List.reverse_reverse,
    List.length_reverse]
  exact (Nat.self_mod_pow_eq_ofDigits_take _ n (by decide : 2 ≤ 10)).symm

theorem digitsToNat_right (n count : Nat) (inside : count ≤ (P37.digitsBE n).length) :
    P37.digitsToNat ((P37.digitsBE n).take ((P37.digitsBE n).length - count)) =
      n / 10 ^ count := by
  rw [digitsToNat_take, Nat.sub_sub_self inside]

theorem digits_length_positive (n : Nat) (positive : 0 < n) :
    0 < (P37.digitsBE n).length := by
  simp only [P37.digitsBE, List.length_reverse, List.length_pos_iff_ne_nil]
  exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)

theorem digits_upper_bound (n : Nat) : n < 10 ^ (P37.digitsBE n).length := by
  simpa [P37.digitsBE] using
    (Nat.digits_length_le_iff (b := 10) (k := (Nat.digits 10 n).length) (by decide) n).mp
      (Nat.le_refl _)

theorem digits_lower_bound (n : Nat) (positive : 0 < n) :
    10 ^ ((P37.digitsBE n).length - 1) ≤ n := by
  have width := digits_length_positive n positive
  apply (Nat.lt_digits_length_iff (b := 10) (k := (P37.digitsBE n).length - 1)
    (by decide) n).mp
  simpa only [P37.digitsBE, List.length_reverse] using
    (show (P37.digitsBE n).length - 1 < (P37.digitsBE n).length by omega)

theorem right_truncation_lt (n count : Nat) (positive : 0 < n) (lower : 0 < count)
    (inside : count ≤ (P37.digitsBE n).length) :
    P37.digitsToNat ((P37.digitsBE n).take ((P37.digitsBE n).length - count)) < n := by
  rw [digitsToNat_right n count inside]
  have power : 10 ≤ 10 ^ count :=
    Nat.pow_le_pow_right (by decide : 0 < 10) (show 1 ≤ count by omega)
  exact Nat.div_lt_self positive (by omega)

theorem left_truncation_lt (n count : Nat) (positive : 0 < n) (lower : 0 < count) :
    P37.digitsToNat ((P37.digitsBE n).drop count) < n := by
  rw [digitsToNat_drop]
  have lowerBound := digits_lower_bound n positive
  have power : 10 ^ ((P37.digitsBE n).length - count) ≤
      10 ^ ((P37.digitsBE n).length - 1) := Nat.pow_le_pow_right (by decide : 0 < 10) (by omega)
  exact Nat.lt_of_lt_of_le (Nat.mod_lt n (Nat.pow_pos (by decide : 0 < 10)))
    (power.trans lowerBound)

def RightPrime (n : Nat) : Prop :=
  ∀ count, 0 < n / 10 ^ count → Nat.Prime (n / 10 ^ count)

theorem reference_rightPrime (n : Nat) (accepted : P37.isTruncatablePrime n = true) :
    RightPrime n := by
  have checks := reference_checks n accepted
  simp only [properChecks, List.all_eq_true, Bool.and_eq_true] at checks
  intro count positive
  by_cases zero : count = 0
  · subst count
    simpa using reference_prime n accepted
  · have inside : count < (P37.digitsBE n).length := by
      by_contra outside
      have power : 10 ^ (P37.digitsBE n).length ≤ 10 ^ count :=
        Nat.pow_le_pow_right (by decide : 0 < 10) (by omega)
      have small := Nat.lt_of_lt_of_le (digits_upper_bound n) power
      rw [Nat.div_eq_of_lt small] at positive
      omega
    have member : count ∈ List.range' 1 ((P37.digitsBE n).length - 1) :=
      List.mem_range'_1.mpr ⟨by omega, by omega⟩
    have prime := (checks count member).2
    rw [digitsToNat_right n count (by omega)] at prime
    exact of_decide_eq_true prime

theorem rightPrime_prime (n : Nat) (positive : 0 < n) (right : RightPrime n) : Nat.Prime n := by
  simpa using right 0 (by simpa using positive)

theorem rightPrime_parent (n : Nat) (right : RightPrime n) : RightPrime (n / 10) := by
  intro count positive
  have equal : n / 10 / 10 ^ count = n / 10 ^ (count + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 10]
  rw [equal] at positive ⊢
  exact right (count + 1) positive

end ProjectEulerStatements.TruncatablePrimes
