import ProjectEulerStatements.P21
import ProjectEulerStatements.Lib.FactorDivisors

/-! Divisor sums after removing a complete prime power. -/
namespace ProjectEulerStatements.DivisorSumFactors

/-- Sum every positive divisor, including the input itself. -/
def sigma (n : Nat) : Nat := ∑ d ∈ n.divisors, d

/-- The geometric term accumulated by repeated prime division. -/
def geometric (p exponent : Nat) : Nat := ∑ k ∈ Finset.range (exponent + 1), p ^ k

@[simp] theorem geometric_zero (p : Nat) : geometric p 0 = 1 := by
  simp [geometric]

theorem geometric_succ (p exponent : Nat) :
    geometric p (exponent + 1) = geometric p exponent + p ^ (exponent + 1) := by
  exact Finset.sum_range_succ _ _

@[simp] theorem sigma_one : sigma 1 = 1 := by
  simp [sigma]

private theorem properDivisors_eq (n : Nat) : P21.properDivisors n = n.properDivisors := by
  ext d
  simp only [P21.properDivisors, Nat.properDivisors, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ico]
  omega

theorem sigma_eq_self_add (n : Nat) (positive : 0 < n) : sigma n = n + P21.d n := by
  simp only [sigma, P21.d, properDivisors_eq]
  rw [← Nat.insert_self_properDivisors positive.ne',
    Finset.sum_insert Nat.self_notMem_properDivisors]

theorem proper_sum_eq (n : Nat) : P21.d n = sigma n - n := by
  by_cases zero : n = 0
  · subst n
    simp [sigma, P21.d, P21.properDivisors]
  · rw [sigma_eq_self_add n (by omega)]
    omega

theorem sigma_prime (p : Nat) (prime : Nat.Prime p) : sigma p = 1 + p := by
  simp [sigma, prime.divisors, prime.ne_one.symm]

theorem sigma_prime_power (p exponent : Nat) (prime : Nat.Prime p) :
    sigma (p ^ exponent) = geometric p exponent := by
  exact Nat.sum_divisors_prime_pow prime

theorem sigma_prime_power_mul (p exponent residue : Nat) (prime : Nat.Prime p)
    (coprime : ¬ p ∣ residue) :
    sigma (p ^ exponent * residue) = geometric p exponent * sigma residue := by
  rw [sigma, (prime.coprime_pow_of_not_dvd coprime).symm.sum_divisors_mul]
  rw [← sigma, sigma_prime_power p exponent prime]
  rfl

/-- The existing stripping theorem also supplies the multiplicative sigma term. -/
theorem strip_sigma (n p : Nat) (positive : 0 < n) (prime : Nat.Prime p) :
    sigma n = geometric p (FactorDivisors.strip n p).2 * sigma (FactorDivisors.strip n p).1 := by
  have spec := FactorDivisors.strip_spec n p positive prime
  conv_lhs => rw [spec.2.2]
  exact sigma_prime_power_mul p _ _ prime spec.2.1

/-- All prime divisors smaller than the next trial candidate have been removed. -/
def NoSmallPrime (n next : Nat) : Prop := ∀ q, Nat.Prime q → q < next → ¬ q ∣ n

theorem trial_prime (n p : Nat) (large : 1 < p) (free : NoSmallPrime n p)
    (divides : p ∣ n) : Nat.Prime p := by
  have prime := Nat.minFac_prime (by omega : p ≠ 1)
  have upper := Nat.minFac_le (by omega : 0 < p)
  have lower : p ≤ p.minFac := by
    by_contra smaller
    exact free p.minFac prime (by omega) ((Nat.minFac_dvd p).trans divides)
  simpa only [Nat.le_antisymm upper lower] using prime

theorem strip_preserves_free (n p next : Nat) (positive : 0 < n) (prime : Nat.Prime p)
    (free : NoSmallPrime n next) : NoSmallPrime (FactorDivisors.strip n p).1 next := by
  intro q primeQ before
  exact FactorDivisors.strip_preserves_not_dvd n p q positive prime (free q primeQ before)

theorem advance_free (n p : Nat) (large : 3 ≤ p) (odd : p % 2 = 1)
    (free : NoSmallPrime n p) (removed : ¬ p ∣ n) : NoSmallPrime n (p + 2) := by
  intro q prime before
  by_cases smaller : q < p
  · exact free q prime smaller
  · have parity := prime.eq_two_or_odd
    have same : q = p := by omega
    simpa only [same] using removed

theorem initial_free (n : Nat) (noTwo : ¬ 2 ∣ n) : NoSmallPrime n 3 := by
  intro q prime before
  have lower := prime.two_le
  have same : q = 2 := by omega
  simpa only [same] using noTwo

theorem finish_sigma (n p : Nat) (positive : 0 < n) (free : NoSmallPrime n p)
    (finished : n < p * p) : sigma n = if 1 < n then 1 + n else 1 := by
  by_cases large : 1 < n
  · have prime : Nat.Prime n := FactorDivisors.prime_of_no_small_factor n large (by
      intro q prime small
      have bound : Nat.sqrt n < p := Nat.sqrt_lt.mpr finished
      exact free q prime (by omega))
    simp [large, sigma_prime n prime]
  · have one : n = 1 := by omega
    simp [one]

end ProjectEulerStatements.DivisorSumFactors
