import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P47

def numDistinctPrimeFactors (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun p => p ≥ 2 ∧ n % p = 0 ∧ Nat.Prime p)).length

/--
Appears to be open problem:
* R. B. Eggleton and J. A. MacDougall, "Consecutive Integers with Equally Many
  Principal Divisors", Math. Mag. 81 (2008), 235-248.
  (Studies fixed-`k` runs for `ω(m)=k`; gives finite upper bounds in several cases.)
* OEIS A064708 (k=2), A087977 (k=4), A087978 (k=5), A185032 (k=3), A185042 (k=4).
  These entries track best-known run lengths/bounds and repeatedly mark large unknown
  regions ("if it exists"), indicating the diagonal statement used here is not settled.
* https://www.reddit.com/r/math/comments/ea4azs/are_there_infinitely_many_consecutive_integers/
* https://mathoverflow.net/questions/52417/consecutive-numbers-with-n-prime-factors
-/
theorem exists_consecutive_with_n_factors (n : Nat) :
    ∃ i, (List.range n).all (fun j => numDistinctPrimeFactors (i + j) = n) := by sorry

/-- Brute-force search for the first number in a run of `n` consecutive integers
each with exactly `n` distinct prime factors. -/
def naive (n : Nat) : Nat :=
  Nat.find (exists_consecutive_with_n_factors n)

example : numDistinctPrimeFactors 14 = 2 := by
  native_decide

example : numDistinctPrimeFactors 15 = 2 := by
  native_decide

example : numDistinctPrimeFactors 644 = 3 := by
  native_decide

example : numDistinctPrimeFactors 645 = 3 := by
  native_decide

example : numDistinctPrimeFactors 646 = 3 := by
  native_decide

example : naive 2 = 14 := by
  native_decide

example : naive 3 = 644 := by
  native_decide

end ProjectEulerStatements.P47
