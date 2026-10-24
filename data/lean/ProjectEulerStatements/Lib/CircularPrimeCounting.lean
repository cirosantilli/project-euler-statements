import ProjectEulerStatements.Lib.CircularPrimeClasses
import Mathlib.Data.Finset.Union

namespace ProjectEulerStatements.CircularPrimes

set_option Elab.async false

theorem circular_prime (n : Nat) (circular : P35.isCircularPrime n = true) : Nat.Prime n := by
  simpa only [digitsToNat_digitsBE] using
    allPrimeRotations_first (circular_allPrimeRotations n circular)

theorem orbit_singleton (n : Nat) (positive : 0 < n) (small : n < 10) : orbit n = {n} := by
  simp [orbit, rotationValues, P35.rotations, P35.digitsBE,
    Nat.digits_of_lt 10 n (by omega) small, P35.digitsToNat]

theorem circular_small_prime (n : Nat) (small : n < 10) (prime : Nat.Prime n) :
    P35.isCircularPrime n = true := by
  have lower := prime.two_le
  simp [P35.isCircularPrime, show ¬ n < 2 by omega, P35.digitsBE,
    Nat.digits_of_lt 10 n (by omega) small, P35.rotations, P35.listAll,
    P35.digitsToNat, P35.isPrime, prime]

def boundedOrbit (limit n : Nat) : Finset Nat := (orbit n).filter (· < limit)

private theorem eraseDups_nodup (items : List Nat) : items.eraseDups.Nodup := by
  induction measure : items.length using Nat.strong_induction_on generalizing items with
  | h size ih =>
      cases items with
      | nil => simp
      | cons head tail =>
          rw [List.eraseDups_cons, List.nodup_cons]
          constructor
          · intro present
            have filtered := List.mem_filter.mp (List.mem_eraseDups.mp present)
            simpa using filtered.2
          · exact ih _ (by
                have := List.length_filter_le (fun n => !(n == head)) tail
                simp only [List.length_cons] at measure
                omega)
              (tail.filter (fun n => !(n == head))) rfl

/-- Counting distinct rotations below a bound is independent of set iteration order. -/
theorem eraseDups_filter_length (n limit : Nat) :
    ((rotationValues n).eraseDups.filter (fun r => decide (r < limit))).length =
      (boundedOrbit limit n).card := by
  have same : ((rotationValues n).eraseDups.filter (fun r => decide (r < limit))).toFinset =
      boundedOrbit limit n := by
    ext r
    simp [boundedOrbit, orbit]
  rw [← same]
  exact (List.toFinset_card_of_nodup
    (List.Nodup.filter (fun r => decide (r < limit)) (eraseDups_nodup (rotationValues n)))).symm

private def OrbitLaws (n : Nat) : Prop :=
  n ∈ orbit n ∧ ∀ other ∈ orbit n, orbit other = orbit n ∧
    (P35.isCircularPrime other = true ↔ P35.isCircularPrime n = true)

private theorem allowed_orbit_laws (n : Nat) (large : 10 ≤ n)
    (allowed : AllowedDigits (P35.digitsBE n)) : OrbitLaws n := by
  refine ⟨mem_orbit_self n (by omega), ?_⟩
  intro other member
  exact ⟨orbit_eq_of_mem n other (by omega) allowed member,
    orbit_circular_iff n other large allowed member⟩

private theorem small_orbit_laws (n : Nat) (positive : 0 < n) (small : n < 10) : OrbitLaws n := by
  refine ⟨mem_orbit_self n positive, ?_⟩
  intro other member
  have equal : other = n := by
    simpa only [orbit_singleton n positive small, Finset.mem_singleton] using member
  subst other
  exact ⟨rfl, Iff.rfl⟩

abbrev CountState := Finset Nat × Nat

/-- Only circular processed values need orbit closure. Rejected singleton
primes and failed cycles contribute nothing to the count. -/
structure CountInvariant (limit : Nat) (state : CountState) : Prop where
  inside : ∀ n ∈ state.1, n < limit
  count : state.2 = (state.1.filter (fun n => P35.isCircularPrime n)).card
  closed : ∀ n ∈ state.1, P35.isCircularPrime n = true → boundedOrbit limit n ⊆ state.1

def algorithmStep (limit : Nat) (state : CountState) (n : Nat) : CountState :=
  if ¬ Nat.Prime n ∨ n ∈ state.1 then state
  else if n < 10 then (insert n state.1, state.2 + 1)
  else if ¬ AllowedDigits (P35.digitsBE n) then (insert n state.1, state.2)
  else (state.1 ∪ boundedOrbit limit n,
    state.2 + if P35.isCircularPrime n then (boundedOrbit limit n).card else 0)

def algorithmFold (limit : Nat) : CountState :=
  (List.range' 2 (limit - 2)).foldl (algorithmStep limit) (∅, 0)

private theorem mark_non_circular (limit : Nat) (state : CountState)
    (invariant : CountInvariant limit state)
    (n : Nat) (inside : n < limit) (notCircular : P35.isCircularPrime n ≠ true) :
    CountInvariant limit (insert n state.1, state.2) := by
  constructor
  · intro other member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact inside
    · exact invariant.inside other member
  · simpa [Finset.filter_insert, notCircular] using invariant.count
  · intro other member circular value inOrbit
    rcases Finset.mem_insert.mp member with rfl | member
    · exact (notCircular circular).elim
    · exact Finset.mem_insert_of_mem (invariant.closed other member circular inOrbit)

private theorem mark_orbit (limit : Nat) (state : CountState)
    (invariant : CountInvariant limit state)
    (n : Nat) (inside : n < limit) (fresh : n ∉ state.1) (laws : OrbitLaws n) :
    CountInvariant limit (state.1 ∪ boundedOrbit limit n,
      state.2 + if P35.isCircularPrime n then (boundedOrbit limit n).card else 0) := by
  have cycleSelf : n ∈ boundedOrbit limit n := Finset.mem_filter.mpr ⟨laws.1, inside⟩
  have equalCycles (other : Nat) (member : other ∈ boundedOrbit limit n) :
      boundedOrbit limit other = boundedOrbit limit n := by
    unfold boundedOrbit
    rw [(laws.2 other (Finset.mem_filter.mp member).1).1]
  have sameCircular (other : Nat) (member : other ∈ boundedOrbit limit n) :
      P35.isCircularPrime other = true ↔ P35.isCircularPrime n = true :=
    (laws.2 other (Finset.mem_filter.mp member).1).2
  constructor
  · intro other member
    rcases Finset.mem_union.mp member with old | added
    · exact invariant.inside other old
    · exact (Finset.mem_filter.mp added).2
  · by_cases circular : P35.isCircularPrime n = true
    · have cycleFilter : (boundedOrbit limit n).filter (fun n => P35.isCircularPrime n) =
          boundedOrbit limit n :=
        Finset.filter_eq_self.mpr (fun other member => (sameCircular other member).mpr circular)
      have disjoint : Disjoint (state.1.filter (fun n => P35.isCircularPrime n))
          (boundedOrbit limit n) := by
        apply Finset.disjoint_left.mpr
        intro other old added
        obtain ⟨old, otherCircular⟩ := Finset.mem_filter.mp old
        have contains := invariant.closed other old otherCircular
        rw [equalCycles other added] at contains
        exact fresh (contains cycleSelf)
      simp only [circular, if_true, Finset.filter_union, cycleFilter,
        Finset.card_union_of_disjoint disjoint, invariant.count]
    · have cycleFilter : (boundedOrbit limit n).filter (fun n => P35.isCircularPrime n) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun other member otherCircular =>
          circular ((sameCircular other member).mp otherCircular))
      simp [circular, Finset.filter_union, cycleFilter, invariant.count]
  · intro other member circular value inOrbit
    rcases Finset.mem_union.mp member with old | added
    · exact Finset.mem_union_left _ (invariant.closed other old circular inOrbit)
    · exact Finset.mem_union_right _ (by rwa [equalCycles other added] at inOrbit)

theorem algorithmStep_invariant (limit : Nat) (state : CountState)
    (invariant : CountInvariant limit state)
    (n : Nat) (inside : n < limit) : CountInvariant limit (algorithmStep limit state n) := by
  by_cases skip : ¬ Nat.Prime n ∨ n ∈ state.1
  · simpa [algorithmStep, skip] using invariant
  · have prime : Nat.Prime n := by by_contra notPrime; exact skip (.inl notPrime)
    have fresh : n ∉ state.1 := fun member => skip (.inr member)
    have positive : 0 < n := prime.pos
    by_cases small : n < 10
    · have marked := mark_orbit limit state invariant n inside fresh
        (small_orbit_laws n positive small)
      have cycle : boundedOrbit limit n = {n} := by
        simp [boundedOrbit, orbit_singleton n positive small, inside]
      simpa [algorithmStep, skip, small, cycle, circular_small_prime n small prime] using marked
    · by_cases allowed : AllowedDigits (P35.digitsBE n)
      · simpa [algorithmStep, skip, small, allowed] using
          mark_orbit limit state invariant n inside fresh (allowed_orbit_laws n (by omega) allowed)
      · have notCircular : P35.isCircularPrime n ≠ true :=
          fun circular => allowed (circular_allowed n (by omega) circular)
        simpa [algorithmStep, skip, small, allowed] using
          mark_non_circular limit state invariant n inside notCircular

theorem algorithmStep_mono (limit : Nat) (state : CountState) (n : Nat) :
    state.1 ⊆ (algorithmStep limit state n).1 := by
  unfold algorithmStep
  split_ifs <;> simp

theorem algorithmStep_covers (limit : Nat) (state : CountState) (n : Nat)
    (inside : n < limit) (circular : P35.isCircularPrime n = true) :
    n ∈ (algorithmStep limit state n).1 := by
  have prime := circular_prime n circular
  have self : n ∈ boundedOrbit limit n :=
    Finset.mem_filter.mpr ⟨mem_orbit_self n prime.pos, inside⟩
  by_cases seen : n ∈ state.1
  · exact algorithmStep_mono limit state n seen
  · by_cases small : n < 10
    · simp [algorithmStep, prime, seen, small]
    · by_cases allowed : AllowedDigits (P35.digitsBE n)
      · simp [algorithmStep, prime, seen, small, allowed, self]
      · simp [algorithmStep, prime, seen, small, allowed]

private theorem fold_mono (limit : Nat) (items : List Nat) (state : CountState) :
    state.1 ⊆ (items.foldl (algorithmStep limit) state).1 := by
  induction items generalizing state with
  | nil => exact Finset.Subset.refl _
  | cons head tail ih => exact (algorithmStep_mono limit state head).trans (ih _)

private theorem fold_invariant (limit : Nat) (items : List Nat) (state : CountState)
    (invariant : CountInvariant limit state) (inside : ∀ n ∈ items, n < limit) :
    CountInvariant limit (items.foldl (algorithmStep limit) state) := by
  induction items generalizing state with
  | nil => exact invariant
  | cons head tail ih =>
      exact ih _ (algorithmStep_invariant limit state invariant head (inside head (by simp)))
        (fun n member => inside n (by simp [member]))

private theorem fold_covers (limit : Nat) (items : List Nat) (state : CountState)
    (inside : ∀ n ∈ items, n < limit) (n : Nat) (member : n ∈ items)
    (circular : P35.isCircularPrime n = true) :
    n ∈ (items.foldl (algorithmStep limit) state).1 := by
  induction items generalizing state with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact fold_mono limit tail _
          (algorithmStep_covers limit state n (inside n (by simp)) circular)
      · exact ih _ (fun n member => inside n (by simp [member])) member

/-- Counting one distinct orbit at a time equals the reference count at every
limit. The proof uses the processed-set invariant, never a finite answer table. -/
theorem algorithmFold_correct (limit : Nat) : (algorithmFold limit).2 = P35.naive limit := by
  have inside : ∀ n ∈ List.range' 2 (limit - 2), n < limit := by
    intro n member
    have bounds := List.mem_range'_1.mp member
    omega
  have initial : CountInvariant limit (∅, 0) := by constructor <;> simp
  have invariant := fold_invariant limit (List.range' 2 (limit - 2)) (∅, 0) initial inside
  change CountInvariant limit (algorithmFold limit) at invariant
  rw [invariant.count]
  change _ = ((Finset.range limit).filter (fun n => P35.isCircularPrime n)).card
  apply congrArg Finset.card
  ext n
  constructor
  · intro member
    obtain ⟨processed, circular⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (invariant.inside n processed), circular⟩
  · intro member
    obtain ⟨bound, circular⟩ := Finset.mem_filter.mp member
    have lower := (circular_prime n circular).two_le
    have scanned : n ∈ List.range' 2 (limit - 2) := by
      apply List.mem_range'_1.mpr
      have bound := Finset.mem_range.mp bound
      omega
    exact Finset.mem_filter.mpr ⟨fold_covers limit _ (∅, 0) inside n scanned circular, circular⟩

end ProjectEulerStatements.CircularPrimes
