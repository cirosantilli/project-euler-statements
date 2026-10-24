import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! Removing prime powers and counting divisors of the remaining coprime factors. -/
namespace ProjectEulerStatements.FactorDivisors

/-- Remove every copy of a factor greater than one, returning the residue and exponent. -/
def strip (n p : Nat) : Nat × Nat :=
  if valid : 1 < p ∧ 0 < n ∧ p ∣ n then
    let result := strip (n / p) p
    (result.1, result.2 + 1)
  else
    (n, 0)
termination_by n
decreasing_by exact Nat.div_lt_self valid.2.1 valid.1

/-- Repeated division ends in a positive residue coprime to the removed prime. -/
theorem strip_spec (n p : Nat) (positive : 0 < n) (prime : Nat.Prime p) :
    0 < (strip n p).1 ∧ ¬ p ∣ (strip n p).1 ∧ n = p ^ (strip n p).2 * (strip n p).1 := by
  by_cases divides : p ∣ n
  · have quotientPositive : 0 < n / p := Nat.div_pos (Nat.le_of_dvd positive divides) prime.pos
    have recurse := strip_spec (n / p) p quotientPositive prime
    rw [strip, dif_pos ⟨prime.one_lt, positive, divides⟩]
    refine ⟨recurse.1, recurse.2.1, ?_⟩
    calc
      n = p * (n / p) := (Nat.mul_div_cancel' divides).symm
      _ = p * (p ^ (strip (n / p) p).2 * (strip (n / p) p).1) :=
        congrArg (p * ·) recurse.2.2
      _ = p ^ ((strip (n / p) p).2 + 1) * (strip (n / p) p).1 := by
        simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]
  · rw [strip, dif_neg (by tauto)]
    simp [positive, divides]
termination_by n
decreasing_by exact Nat.div_lt_self positive prime.one_lt

theorem strip_dvd (n p : Nat) (positive : 0 < n) (prime : Nat.Prime p) :
    (strip n p).1 ∣ n := by
  refine ⟨p ^ (strip n p).2, ?_⟩
  simpa only [Nat.mul_comm] using (strip_spec n p positive prime).2.2

theorem strip_le (n p : Nat) (positive : 0 < n) (prime : Nat.Prime p) :
    (strip n p).1 ≤ n := Nat.le_of_dvd positive (strip_dvd n p positive prime)

/-- Removing a factor cannot introduce a previously excluded divisor. -/
theorem strip_preserves_not_dvd (n p q : Nat) (positive : 0 < n) (prime : Nat.Prime p)
    (excluded : ¬ q ∣ n) : ¬ q ∣ (strip n p).1 :=
  fun divides => excluded (divides.trans (strip_dvd n p positive prime))

/-- Divisor counts multiply after removing a complete prime power. -/
theorem prime_power_mul (p exponent residue : Nat) (prime : Nat.Prime p)
    (coprime : ¬ p ∣ residue) :
    (p ^ exponent * residue).divisors.card = (exponent + 1) * residue.divisors.card := by
  rw [(prime.coprime_pow_of_not_dvd coprime).symm.card_divisors_mul]
  simp [Nat.divisors_prime_pow prime, Finset.card_map]

theorem strip_divisor_count (n p : Nat) (positive : 0 < n) (prime : Nat.Prime p) :
    n.divisors.card = ((strip n p).2 + 1) * (strip n p).1.divisors.card := by
  have spec := strip_spec n p positive prime
  calc
    n.divisors.card = (p ^ (strip n p).2 * (strip n p).1).divisors.card :=
      congrArg (fun k : Nat => k.divisors.card) spec.2.2
    _ = _ := prime_power_mul p (strip n p).2 (strip n p).1 prime spec.2.1

/-- A residue above one is prime once every prime up to its square root is excluded. -/
theorem prime_of_no_small_factor (n : Nat) (large : 1 < n)
    (excluded : ∀ p, Nat.Prime p → p ≤ Nat.sqrt n → ¬ p ∣ n) : Nat.Prime n := by
  by_contra composite
  have factorPrime := Nat.minFac_prime (by omega : n ≠ 1)
  have small : n.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr
    (Nat.minFac_sq_le_self (by omega : 0 < n) composite)
  exact excluded n.minFac factorPrime small (Nat.minFac_dvd n)

/-- A checked prefix suffices when every unvisited cached prime exceeds the square root. -/
theorem prime_of_checked_prefix (n : Nat) (ps : List Nat) (position : Nat) (large : 1 < n)
    (complete : ∀ p, Nat.Prime p → p ≤ Nat.sqrt n → p ∈ ps)
    (checked : ∀ p ∈ ps.take position, ¬ p ∣ n)
    (beyond : ∀ p ∈ ps.drop position, Nat.sqrt n < p) : Nat.Prime n := by
  apply prime_of_no_small_factor n large
  intro p prime small
  have member := complete p prime small
  have partition : p ∈ ps.take position ∨ p ∈ ps.drop position := by
    rw [← List.mem_append, List.take_append_drop]
    exact member
  rcases partition with visited | pending
  · exact checked p visited
  · have far := beyond p pending
    omega

def finish (n : Nat) : Nat := if 1 < n then 2 else 1

/-- Trial division with a shrinking residue and an early square bound. -/
def count (n : Nat) : List Nat → Nat
  | [] => finish n
  | p :: rest =>
      if n < p * p then finish n
      else ((strip n p).2 + 1) * count (strip n p).1 rest

/-- The remaining residue contributes either one or two divisors. -/
theorem finish_correct (n : Nat) (positive : 0 < n)
    (excluded : ∀ p, Nat.Prime p → p ≤ Nat.sqrt n → ¬ p ∣ n) :
    finish n = n.divisors.card := by
  by_cases large : 1 < n
  · have prime := prime_of_no_small_factor n large excluded
    simp [finish, large, prime.divisors, prime.ne_one.symm]
  · have equal : n = 1 := by omega
    simp [equal, finish]

/-- Only the possible small prime divisors need to remain in the cache. -/
theorem count_correct (n : Nat) (ps : List Nat) (positive : 0 < n)
    (ordered : ps.Pairwise (· ≤ ·)) (primes : ∀ p ∈ ps, Nat.Prime p)
    (complete : ∀ p, Nat.Prime p → p ≤ Nat.sqrt n → p ∣ n → p ∈ ps) :
    count n ps = n.divisors.card := by
  induction ps generalizing n with
  | nil =>
      apply finish_correct n positive
      intro p prime small divides
      exact List.not_mem_nil (complete p prime small divides)
  | cons p rest ih =>
      obtain ⟨after, ordered⟩ := List.pairwise_cons.mp ordered
      have prime := primes p (by simp)
      have primesRest (q : Nat) (member : q ∈ rest) : Nat.Prime q := primes q (by simp [member])
      by_cases stop : n < p * p
      · rw [count, if_pos stop]
        apply finish_correct n positive
        intro q primeQ small divides
        have member := complete q primeQ small divides
        have beyond : Nat.sqrt n < p := Nat.sqrt_lt.mpr stop
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · have lower := after q member
          omega
      · rw [count, if_neg stop]
        have spec := strip_spec n p positive prime
        have nextComplete (q : Nat) (primeQ : Nat.Prime q)
            (small : q ≤ Nat.sqrt (strip n p).1) (divides : q ∣ (strip n p).1) : q ∈ rest := by
          have oldSmall := small.trans (Nat.sqrt_le_sqrt (strip_le n p positive prime))
          have member := complete q primeQ oldSmall (divides.trans (strip_dvd n p positive prime))
          rcases List.mem_cons.mp member with rfl | member
          · exact False.elim (spec.2.1 divides)
          · exact member
        rw [ih (strip n p).1 spec.1 ordered primesRest nextComplete]
        exact (strip_divisor_count n p positive prime).symm

end ProjectEulerStatements.FactorDivisors
