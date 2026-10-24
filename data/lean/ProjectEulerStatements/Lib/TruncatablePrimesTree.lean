import ProjectEulerStatements.Lib.TruncatablePrimesDigits
import ProjectEulerStatements.Lib.CircularPrimeOrbits
import Mathlib.Tactic.NormNum.Prime

/-! A bounded right-truncatable-prime tree. Completeness follows by deleting
the final decimal digit, rather than checking every number below the bound. -/
namespace ProjectEulerStatements.TruncatablePrimes

set_option Elab.async false

def roots : List Nat := [2, 3, 5, 7]

def children (n : Nat) : List Nat :=
  ([1, 3, 7, 9].map (fun digit => 10 * n + digit)).filter P37.isPrime

/-- `tree depth` contains right-truncatable primes with at most `depth + 1` digits. -/
def tree : Nat → List Nat
  | 0 => roots
  | depth + 1 => roots ++ (tree depth).flatMap children

theorem prime_small_mem_roots (n : Nat) (small : n < 10) (prime : Nat.Prime n) :
    n ∈ roots := by
  interval_cases n <;> norm_num [roots] at *

theorem rightPrime_mem_tree (depth n : Nat) (positive : 0 < n)
    (bound : n < 10 ^ (depth + 1)) (right : RightPrime n) : n ∈ tree depth := by
  induction depth generalizing n with
  | zero => exact prime_small_mem_roots n bound (rightPrime_prime n positive right)
  | succ depth ih =>
      have prime := rightPrime_prime n positive right
      by_cases small : n < 10
      · exact List.mem_append_left _ (prime_small_mem_roots n small prime)
      · have large : 10 ≤ n := by omega
        have parentPositive : 0 < n / 10 := Nat.div_pos large (by decide)
        have parentBound : n / 10 < 10 ^ (depth + 1) := by
          apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).mpr
          simpa only [Nat.pow_succ] using bound
        have parent := ih (n / 10) parentPositive parentBound (rightPrime_parent n right)
        have digit := CircularPrimes.prime_last_digit n large prime
        have digitMember : n % 10 ∈ ([1, 3, 7, 9] : List Nat) := by
          simpa using digit
        have composed : 10 * (n / 10) + n % 10 = n := by omega
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨n / 10, parent,
          List.mem_filter.mpr ⟨List.mem_map.mpr ⟨n % 10, digitMember, composed⟩,
            decide_eq_true prime⟩⟩)

theorem reference_mem_tree (n : Nat) (bound : n < 1000000)
    (accepted : P37.isTruncatablePrime n = true) : n ∈ tree 5 :=
  rightPrime_mem_tree 5 n (by have := reference_large n accepted; omega) bound
    (reference_rightPrime n accepted)

end ProjectEulerStatements.TruncatablePrimes
