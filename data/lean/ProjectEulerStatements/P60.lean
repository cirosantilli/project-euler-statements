import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P60

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

/-- Concatenate two numbers in base 10. -/
def concat (a b : Nat) : Nat :=
  a * 10 ^ (Nat.digits 10 b).length + b

/-- Whether two primes concatenate to primes in both orders. -/
def goodPair (a b : Nat) : Bool :=
  isPrime (concat a b) && isPrime (concat b a)

/-- All unordered pairs in a list satisfy `goodPair`. -/
def allPairsGood : List Nat → Bool
  | [] => true
  | x :: xs => (xs.all (fun y => goodPair x y)) && allPairsGood xs

/-- All elements are prime. -/
def allPrime (s : List Nat) : Bool :=
  s.all isPrime

/-- A prime pair set: primes, and any concatenation is prime. -/
def isPrimePairSet (s : List Nat) : Bool :=
  allPrime s && allPairsGood s

/-- Existence of a prime pair set of size `k`. -/
theorem exists_pair_set (k : Nat) : ∃ s : List Nat, s.length = k ∧ isPrimePairSet s = true := by
  sorry

def hasPairSum (k n : Nat) : Prop :=
  ∃ s : List Nat, s.length = k ∧ isPrimePairSet s = true ∧ s.sum = n

theorem exists_pair_sum (k : Nat) : ∃ n, hasPairSum k n := by
  rcases exists_pair_set k with ⟨s, hs, hgood⟩
  exact ⟨s.sum, ⟨s, hs, hgood, rfl⟩⟩

/-- Smallest sum of a prime pair set of size `k`. -/
noncomputable def naive (k : Nat) : Nat := by
  classical
  exact Nat.find (exists_pair_sum k)

end ProjectEulerStatements.P60
