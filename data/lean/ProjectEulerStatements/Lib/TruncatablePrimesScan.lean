import ProjectEulerStatements.Lib.TruncatablePrimesCertificate
import Mathlib.Data.List.Sort

/-! The exact eleven-value reference interval and the source's early exit.
The scan proof is generic in its remaining list and accumulated results. -/
namespace ProjectEulerStatements.TruncatablePrimes

set_option Elab.async false

theorem reference_iff_mem_values (n : Nat) (bound : n < 1000000) :
    P37.isTruncatablePrime n = true ↔ n ∈ values := by
  constructor
  · intro accepted
    rw [← tree_accepted]
    exact List.mem_filter.mpr ⟨reference_mem_tree n bound accepted, accepted⟩
  · intro member
    rw [← tree_accepted] at member
    exact (List.mem_filter.mp member).2

theorem value_accepted (n : Nat) (member : n ∈ values) :
    P37.isTruncatablePrime n = true := by
  rw [← tree_accepted] at member
  exact (List.mem_filter.mp member).2

theorem value_bounds (n : Nat) (member : n ∈ values) : 11 ≤ n ∧ n < 1000000 := by
  exact of_decide_eq_true (List.all_eq_true.mp values_bounds n member)

theorem reference_odd (n : Nat) (accepted : P37.isTruncatablePrime n = true) : n % 2 = 1 := by
  have large := reference_large n accepted
  rcases (reference_prime n accepted).eq_two_or_odd with two | odd <;> omega

theorem values_sorted : values.Pairwise (· < ·) := by decide +kernel

theorem reference_values : (List.range 1000000).filter P37.isTruncatablePrime = values := by
  apply (List.pairwise_lt_range.filter P37.isTruncatablePrime).eq_of_mem_iff values_sorted
  intro n
  constructor
  · intro member
    obtain ⟨inside, accepted⟩ := List.mem_filter.mp member
    exact (reference_iff_mem_values n (List.mem_range.mp inside)).mp accepted
  · intro member
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (value_bounds n member).2,
      value_accepted n member⟩

theorem reference_value : P37.naive 1000000 = 748317 := by
  rw [naive_filter_sum, reference_values, values_sum]

def searchCandidates : List Nat := List.range' 11 499995 2

theorem mem_searchCandidates (n : Nat) :
    n ∈ searchCandidates ↔ 11 ≤ n ∧ n < 1000000 ∧ n % 2 = 1 := by
  simp only [searchCandidates, List.mem_range']
  constructor
  · rintro ⟨index, bound, rfl⟩
    omega
  · rintro ⟨lower, upper, odd⟩
    refine ⟨(n - 11) / 2, ?_, ?_⟩ <;> omega

theorem search_values : searchCandidates.filter P37.isTruncatablePrime = values := by
  apply (List.pairwise_lt_range' 2 (by decide)).filter P37.isTruncatablePrime
    |>.eq_of_mem_iff values_sorted
  intro n
  constructor
  · intro member
    obtain ⟨inside, accepted⟩ := List.mem_filter.mp member
    exact (reference_iff_mem_values n ((mem_searchCandidates n).mp inside).2.1).mp accepted
  · intro member
    have bounds := value_bounds n member
    have accepted := value_accepted n member
    exact List.mem_filter.mpr ⟨(mem_searchCandidates n).mpr
      ⟨bounds.1, bounds.2, reference_odd n accepted⟩, accepted⟩

/-- The Python loop breaks just after appending its eleventh accepted value. -/
def collectUntilEleven : List Nat → List Nat → List Nat
  | [], found => found
  | n :: rest, found =>
      if P37.isTruncatablePrime n then
        let next := found ++ [n]
        if next.length = 11 then next else collectUntilEleven rest next
      else collectUntilEleven rest found

theorem collectUntilEleven_complete (items found : List Nat)
    (bound : found.length + (items.filter P37.isTruncatablePrime).length ≤ 11) :
    collectUntilEleven items found = found ++ items.filter P37.isTruncatablePrime := by
  induction items generalizing found with
  | nil => simp [collectUntilEleven]
  | cons head tail ih =>
      by_cases accepted : P37.isTruncatablePrime head = true
      · simp only [List.filter_cons, accepted, if_true, List.length_cons] at bound
        by_cases finished : (found ++ [head]).length = 11
        · have empty : (tail.filter P37.isTruncatablePrime).length = 0 := by
            simp only [List.length_append, List.length_singleton] at finished
            omega
          have noMore := List.length_eq_zero_iff.mp empty
          simp [collectUntilEleven, accepted, finished, List.filter, noMore]
        · have remaining : (found ++ [head]).length +
              (tail.filter P37.isTruncatablePrime).length ≤ 11 := by
            simp only [List.length_append, List.length_singleton]
            omega
          simp only [collectUntilEleven, accepted, if_true, if_neg finished,
            List.filter_cons, ih _ remaining, List.append_assoc, List.singleton_append]
      · have remaining : found.length + (tail.filter P37.isTruncatablePrime).length ≤ 11 := by
          simpa [List.filter, accepted] using bound
        simpa [collectUntilEleven, accepted, List.filter] using ih found remaining

theorem collectUntilEleven_empty (items : List Nat)
    (bound : (items.filter P37.isTruncatablePrime).length ≤ 11) :
    collectUntilEleven items [] = items.filter P37.isTruncatablePrime := by
  simpa only [List.nil_append] using
    collectUntilEleven_complete items [] (by simpa only [List.length_nil, Nat.zero_add] using bound)

theorem collected_values : collectUntilEleven searchCandidates [] = values := by
  have bound : (searchCandidates.filter P37.isTruncatablePrime).length ≤ 11 := by
    rw [search_values, values_length]
  exact (collectUntilEleven_empty searchCandidates bound).trans search_values

theorem collected_sum : (collectUntilEleven searchCandidates []).sum = P37.naive 1000000 := by
  rw [collected_values, values_sum, reference_value]

theorem example_proper : properTruncatable 3797 = true := by
  have accepted := value_accepted 3797 (by decide +kernel)
  rw [reference_eq_prime_and_proper, Bool.and_eq_true] at accepted
  exact accepted.2

end ProjectEulerStatements.TruncatablePrimes
