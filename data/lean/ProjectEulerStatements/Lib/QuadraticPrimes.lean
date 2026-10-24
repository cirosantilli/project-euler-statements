import ProjectEulerStatements.P27
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Finite prime runs for monic integral quadratics and safe search pruning. -/
namespace ProjectEulerStatements.QuadraticPrimes
open P27

theorem prime_iff (value : Int) :
    isPrimeInt value = true ↔ 1 < value ∧ Nat.Prime value.toNat := by
  simp [isPrimeInt]

/-- A prime value at zero and one forces a composite value by index `b`. -/
theorem failure_before_bound (a b : Int) :
    ∃ n : Nat, n < consecPrimeBound b ∧ isPrimeInt (quad a b n) = false := by
  by_cases atZero : isPrimeInt b = true
  · have positive := (prime_iff b).mp atZero
    lift b to Nat using (by omega : 0 ≤ b)
    by_cases atOne : isPrimeInt (quad a b 1) = true
    · have nextPositive := ((prime_iff _).mp atOne).1
      have factor : 1 < (b : Int) + a + 1 := by
        simp only [quad, Nat.cast_one, mul_one] at nextPositive
        omega
      obtain ⟨c, equal⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (b : Int) + a + 1)
      have composite : ¬ Nat.Prime (b * c) := Nat.not_prime_mul (by omega) (by omega)
      refine ⟨b, by simp [consecPrimeBound], ?_⟩
      have value : quad a b b = ((b * c : Nat) : Int) := by
        dsimp [quad]
        rw [← equal]
        ring
      rw [value]
      simp only [isPrimeInt, Int.toNat_natCast, composite, decide_false, Bool.and_false]
    · refine ⟨1, by simp [consecPrimeBound]; omega, ?_⟩
      exact Bool.eq_false_iff.mpr atOne
  · exact ⟨0, by simp [consecPrimeBound], by simpa [quad] using Bool.eq_false_iff.mpr atZero⟩

private theorem exists_failure (a b : Int) : ∃ n : Nat, isPrimeInt (quad a b n) = false := by
  obtain ⟨n, _, failure⟩ := failure_before_bound a b
  exact ⟨n, failure⟩

/-- The first nonprime value in the unbounded source search. -/
noncomputable def first (a b : Int) : Nat := Nat.find (exists_failure a b)

theorem first_spec (a b : Int) : isPrimeInt (quad a b (first a b)) = false :=
  Nat.find_spec (exists_failure a b)

theorem before_first (a b : Int) (n : Nat) (before : n < first a b) :
    isPrimeInt (quad a b n) = true := by
  have noFailure := Nat.find_min (exists_failure a b) before
  exact Bool.eq_true_of_not_eq_false noFailure

theorem first_le (a b : Int) (n : Nat) (failure : isPrimeInt (quad a b n) = false) :
    first a b ≤ n := Nat.find_min' (exists_failure a b) failure

theorem first_lt_bound (a b : Int) : first a b < consecPrimeBound b := by
  obtain ⟨n, bound, failure⟩ := failure_before_bound a b
  exact (first_le a b n failure).trans_lt bound

/-- The bounded reference counts exactly the distance to the first failure. -/
theorem scan_first (a b : Int) (n fuel : Nat) (before : n ≤ first a b)
    (enough : first a b < n + fuel) : n + consecPrimeLen.go a b n fuel = first a b := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      rw [consecPrimeLen.go]
      by_cases same : n = first a b
      · subst n
        simp [first_spec]
      · have smaller : n < first a b := by omega
        rw [before_first a b n smaller]
        simp only [↓reduceIte]
        have rest := ih (n + 1) (by omega) (by omega)
        omega

theorem consecPrimeLen_eq_first (a b : Int) : consecPrimeLen a b = first a b := by
  simpa only [Nat.zero_add] using
    scan_first a b 0 (consecPrimeBound b) (by omega) (by simpa using first_lt_bound a b)

/-- The quick check at index one excludes at most a one-prime prefix. -/
theorem quick_prune (a b : Int) (failure : isPrimeInt (1 + a + b) = false) :
    consecPrimeLen a b ≤ 1 := by
  rw [consecPrimeLen_eq_first]
  apply first_le a b 1
  simpa [quad] using failure

theorem nonprime_b (a b : Int) (failure : isPrimeInt b = false) : consecPrimeLen a b = 0 := by
  rw [consecPrimeLen_eq_first]
  exact Nat.eq_zero_of_le_zero (first_le a b 0 (by simpa [quad] using failure))

private theorem prime_parity (value : Int) (prime : isPrimeInt value = true) :
    value = 2 ∨ value % 2 = 1 := by
  obtain ⟨positive, prime⟩ := (prime_iff value).mp prime
  lift value to Nat using (by omega : 0 ≤ value)
  simp only [Int.toNat_natCast] at prime
  rcases prime.eq_two_or_odd with two | odd
  · left; exact_mod_cast two
  · right; exact_mod_cast odd

private theorem even_prime (value : Int) (prime : isPrimeInt value = true)
    (even : value % 2 = 0) : value = 2 := by
  rcases prime_parity value prime with two | odd
  · exact two
  · omega

/-- Parity pruning for odd `b` can discard a three-prime run: `a = -2, b = 3`. -/
theorem odd_b_even_a (a b : Int) (primeB : isPrimeInt b = true)
    (notTwo : b ≠ 2) (evenA : a % 2 = 0) : consecPrimeLen a b ≤ 3 := by
  by_cases atOne : isPrimeInt (quad a b 1) = true
  · have oddB : b % 2 = 1 := (prime_parity b primeB).resolve_left notTwo
    have valueTwo := even_prime (quad a b 1) atOne (by dsimp [quad]; omega)
    have coefficient : a = 1 - b := by dsimp [quad] at valueTwo; omega
    have positive := ((prime_iff b).mp primeB).1
    rw [consecPrimeLen_eq_first]
    by_cases three : b = 3
    · have aValue : a = -2 := by omega
      apply first_le a b 3
      norm_num [quad, isPrimeInt, aValue, three]
      decide
    · have large : 5 ≤ b := by omega
      have small : quad a b 2 ≤ 1 := by dsimp [quad]; omega
      have failure : isPrimeInt (quad a b 2) = false := by
        simp [isPrimeInt, show ¬ 1 < quad a b 2 by omega]
      exact (first_le a b 2 failure).trans (by decide)
  · have failure : isPrimeInt (1 + a + b) = false := by
      simpa [quad] using Bool.eq_false_iff.mpr atOne
    exact (quick_prune a b failure).trans (by decide)

/-- For `b = 2`, an odd coefficient can contribute at most two initial primes. -/
theorem two_b_odd_a (a : Int) (oddA : a % 2 ≠ 0) : consecPrimeLen a 2 ≤ 2 := by
  by_cases atOne : isPrimeInt (quad a 2 1) = true
  · have valueTwo := even_prime (quad a 2 1) atOne (by dsimp [quad]; omega)
    have coefficient : a = -1 := by dsimp [quad] at valueTwo; omega
    rw [consecPrimeLen_eq_first]
    apply first_le a 2 2
    norm_num [quad, isPrimeInt, coefficient]
    decide
  · have failure : isPrimeInt (1 + a + 2) = false := by
      simpa [quad] using Bool.eq_false_iff.mpr atOne
    exact (quick_prune a 2 failure).trans (by decide)

/-- A surviving small candidate already exceeds every parity-pruned run. -/
theorem baseline : consecPrimeLen (-1) 5 = 5 := by
  norm_num [consecPrimeLen, consecPrimeLen.go, consecPrimeBound, quad, isPrimeInt]
  decide

end ProjectEulerStatements.QuadraticPrimes
