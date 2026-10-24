import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

/-! Trial division against an ordered prime cache, with an early square-root exit. -/
namespace ProjectEulerStatements.PrimeTrialDivision

def trial (n : Nat) : List Nat → Bool
  | [] => true
  | p :: rest =>
      if Nat.sqrt n < p then true
      else if n % p = 0 then false
      else trial n rest

/-- Ordering makes the early exit equivalent to checking every small entry. -/
theorem trial_eq_true_iff (n : Nat) (ps : List Nat) (ordered : ps.Pairwise (· ≤ ·)) :
    trial n ps = true ↔ ∀ p ∈ ps, p ≤ Nat.sqrt n → n % p ≠ 0 := by
  induction ps with
  | nil => simp [trial]
  | cons p rest ih =>
      obtain ⟨after, ordered⟩ := List.pairwise_cons.mp ordered
      by_cases stop : Nat.sqrt n < p
      · simp only [trial, if_pos stop, true_iff]
        intro q member bounded
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · have lower := after q member
          omega
      · by_cases divides : n % p = 0
        · simp only [trial, if_neg stop, if_pos divides, Bool.false_eq_true, false_iff]
          intro checked
          exact checked p (by simp) (by omega) divides
        · simp only [trial, if_neg stop, if_neg divides, ih ordered]
          constructor
          · intro checked q member bounded
            rcases List.mem_cons.mp member with rfl | member
            · exact divides
            · exact checked q member bounded
          · intro checked q member bounded
            exact checked q (by simp [member]) bounded

/-- Every composite has a prime divisor at most its square root. -/
theorem trial_correct (n : Nat) (ps : List Nat) (large : 2 ≤ n)
    (ordered : ps.Pairwise (· ≤ ·))
    (primes : ∀ p ∈ ps, Nat.Prime p)
    (complete : ∀ p, Nat.Prime p → p ≤ Nat.sqrt n → p ∈ ps) :
    trial n ps = decide (Nat.Prime n) := by
  by_cases prime : Nat.Prime n
  · simp only [prime, decide_true]
    apply (trial_eq_true_iff n ps ordered).mpr
    intro p member bounded divides
    exact (Nat.prime_def_le_sqrt.mp prime).2 p (primes p member).two_le bounded
      (Nat.dvd_of_mod_eq_zero divides)
  · simp only [prime, decide_false]
    apply Bool.eq_false_iff.mpr
    intro tested
    have factorPrime := Nat.minFac_prime (by omega : n ≠ 1)
    have small : n.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr
      (Nat.minFac_sq_le_self (by omega : 0 < n) prime)
    exact (trial_eq_true_iff n ps ordered).mp tested n.minFac
      (complete n.minFac factorPrime small) small (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))

def CompleteBelow (ps : List Nat) (bound : Nat) : Prop :=
  ∀ p, p ∈ ps ↔ Nat.Prime p ∧ p < bound

theorem initial : CompleteBelow [2] 3 := by
  intro p
  constructor
  · intro member
    have equal : p = 2 := by simpa using member
    subst p
    exact ⟨Nat.prime_two, by omega⟩
  · rintro ⟨prime, bounded⟩
    have lower := prime.two_le
    have equal : p = 2 := by omega
    simp [equal]

/-- A complete cache below the candidate suffices for its primality test. -/
theorem trial_complete (n : Nat) (ps : List Nat) (large : 2 ≤ n)
    (ordered : ps.Pairwise (· ≤ ·)) (complete : CompleteBelow ps n) :
    trial n ps = decide (Nat.Prime n) := by
  apply trial_correct n ps large ordered
  · intro p member
    exact ((complete p).mp member).1
  · intro p prime bounded
    exact (complete p).mpr ⟨prime, lt_of_le_of_lt bounded (Nat.sqrt_lt_self (by omega))⟩

/-- Checking one odd candidate advances completeness past the next even number. -/
theorem advance_complete (n : Nat) (ps : List Nat) (large : 3 ≤ n) (odd : n % 2 = 1)
    (complete : CompleteBelow ps n) :
    CompleteBelow (if Nat.Prime n then ps ++ [n] else ps) (n + 2) := by
  have noBetween (p : Nat) (prime : Nat.Prime p) (bounded : p < n + 2) : p ≤ n := by
    rcases prime.eq_two_or_odd with two | oddPrime <;> omega
  intro p
  by_cases prime : Nat.Prime n
  · simp only [if_pos prime, List.mem_append, List.mem_singleton, complete p]
    constructor
    · rintro (⟨primeP, bounded⟩ | rfl)
      · exact ⟨primeP, by omega⟩
      · exact ⟨prime, by omega⟩
    · rintro ⟨primeP, bounded⟩
      have below := noBetween p primeP bounded
      by_cases same : p = n
      · exact Or.inr same
      · exact Or.inl ⟨primeP, by omega⟩
  · simp only [if_neg prime, complete p]
    constructor
    · rintro ⟨primeP, bounded⟩
      exact ⟨primeP, by omega⟩
    · rintro ⟨primeP, bounded⟩
      have below := noBetween p primeP bounded
      have different : p ≠ n := fun equal => prime (equal ▸ primeP)
      exact ⟨primeP, by omega⟩

theorem advance_ordered (n : Nat) (ps : List Nat) (ordered : ps.Pairwise (· < ·))
    (complete : CompleteBelow ps n) :
    (if Nat.Prime n then ps ++ [n] else ps).Pairwise (· < ·) := by
  split
  · apply List.pairwise_append.mpr
    refine ⟨ordered, by simp, ?_⟩
    intro p member q last
    have same : q = n := by simpa using last
    subst q
    exact ((complete p).mp member).2
  · exact ordered

def nextCandidate (p : Nat) : Nat := if (p + 1) % 2 = 0 then p + 2 else p + 1

theorem nextCandidate_spec (p : Nat) (large : 2 ≤ p) :
    p < nextCandidate p ∧ 3 ≤ nextCandidate p ∧ nextCandidate p % 2 = 1 := by
  unfold nextCandidate
  split <;> omega

/-- Starting after the last cached prime skips at most one composite even number. -/
theorem nextCandidate_complete (p : Nat) (ps : List Nat) (prime : Nat.Prime p)
    (complete : CompleteBelow ps (p + 1)) : CompleteBelow ps (nextCandidate p) := by
  have large := prime.two_le
  unfold nextCandidate
  split
  · rename_i even
    intro q
    rw [complete q]
    constructor
    · rintro ⟨primeQ, bounded⟩
      exact ⟨primeQ, by omega⟩
    · rintro ⟨primeQ, bounded⟩
      refine ⟨primeQ, ?_⟩
      rcases primeQ.eq_two_or_odd with two | odd <;> omega
  · exact complete

/-- Every cached entry is at most the last entry of an ordered cache. -/
theorem member_le_last (ps : List Nat) (last p : Nat) (ordered : ps.Pairwise (· ≤ ·))
    (lastEntry : ps.getLast? = some last) (member : p ∈ ps) : p ≤ last := by
  have upper := ordered.rel_getLast member
  have lastValue : ps.getLast (List.ne_nil_of_mem member) = last :=
    List.getLast_of_mem_getLast? lastEntry
  rwa [lastValue] at upper

/-- Completeness at a candidate implies completeness through the last cached prime. -/
theorem complete_at_last (ps : List Nat) (last candidate : Nat)
    (ordered : ps.Pairwise (· ≤ ·)) (lastEntry : ps.getLast? = some last)
    (complete : CompleteBelow ps candidate) : CompleteBelow ps (last + 1) := by
  have lastMember : last ∈ ps := List.mem_of_mem_getLast? lastEntry
  have below := ((complete last).mp lastMember).2
  intro p
  constructor
  · intro member
    refine ⟨((complete p).mp member).1, ?_⟩
    have := member_le_last ps last p ordered lastEntry member
    omega
  · rintro ⟨prime, bounded⟩
    exact (complete p).mpr ⟨prime, by omega⟩

/-- While the cache is too short, its candidate cannot have passed a larger prime. -/
theorem candidate_le_prime (ps : List Nat) (last candidate target bound : Nat)
    (ordered : ps.Pairwise (· ≤ ·)) (lastEntry : ps.getLast? = some last)
    (complete : CompleteBelow ps candidate) (short : last < target)
    (enough : target ≤ bound) (prime : Nat.Prime bound) : candidate ≤ bound := by
  by_contra tooFar
  have member := (complete bound).mpr ⟨prime, by omega⟩
  have upper := member_le_last ps last bound ordered lastEntry member
  omega

/-- Euclid supplies a decreasing measure for every requested cache size. -/
theorem extension_bound (target : Nat) : ∃ bound, Nat.Prime bound ∧ target ≤ bound ∧
    ∀ ps last candidate, ps.Pairwise (· ≤ ·) → ps.getLast? = some last →
      CompleteBelow ps candidate → last < target →
      bound + 2 - (candidate + 2) < bound + 2 - candidate := by
  obtain ⟨bound, enough, prime⟩ := Nat.exists_infinite_primes target
  refine ⟨bound, prime, enough, ?_⟩
  intro ps last candidate ordered lastEntry complete short
  have below := candidate_le_prime ps last candidate target bound
    ordered lastEntry complete short enough prime
  omega

end ProjectEulerStatements.PrimeTrialDivision
