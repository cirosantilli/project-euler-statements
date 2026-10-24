import ProjectEulerStatements.P37
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Exact reference sums and the optimized predicate on proper truncations.
The optimized helper deliberately leaves primality of the input to its caller. -/
namespace ProjectEulerStatements.TruncatablePrimes

set_option Elab.async false

theorem listAll_eq_all (items : List Bool) : P37.listAll items = items.all id := by
  have fold (items : List Bool) (initial : Bool) :
      items.foldl (fun acc value => acc && value) initial = (initial && items.all id) := by
    induction items generalizing initial with
    | nil => simp
    | cons head tail ih => simp [List.foldl, ih, Bool.and_assoc]
  simpa [P37.listAll] using fold items true

theorem listAll_map_eq_all (items : List α) (predicate : α → Bool) :
    P37.listAll (items.map predicate) = items.all predicate := by
  simp [listAll_eq_all, List.all_map, Function.comp_def]

theorem fold_filter_sum (items : List Nat) (predicate : Nat → Bool) (initial : Nat) :
    items.foldl (fun total n => if predicate n then total + n else total) initial =
      initial + (items.filter predicate).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      cases selected : predicate head <;>
        simp [List.foldl, List.filter, selected, ih, Nat.add_assoc]

theorem naive_filter_sum (limit : Nat) :
    P37.naive limit = ((List.range limit).filter P37.isTruncatablePrime).sum := by
  have same : ((List.range limit).filter P37.isTruncatablePrime).toFinset =
      (Finset.range limit).filter (fun n => P37.isTruncatablePrime n) := by
    ext n
    simp
  unfold P37.naive P37.sumTruncatable
  rw [← same, List.sum_toFinset]
  · simp
  · exact List.Nodup.filter _ List.nodup_range

theorem naive_fold (limit : Nat) :
    P37.naive limit = (List.range limit).foldl
      (fun total n => if P37.isTruncatablePrime n then total + n else total) 0 := by
  simp [fold_filter_sum, naive_filter_sum]

def properChecks (n : Nat) : Bool :=
  let ds := P37.digitsBE n
  (List.range' 1 (ds.length - 1)).all (fun i =>
    P37.isPrime (P37.digitsToNat (ds.drop i)) &&
      P37.isPrime (P37.digitsToNat (ds.take (ds.length - i))))

def properTruncatable (n : Nat) : Bool := if n < 10 then false else properChecks n

theorem properChecks_eq_all (n : Nat) :
    properChecks n = P37.listAll ((P37.truncations n).map P37.isPrime) := by
  apply Bool.eq_iff_iff.mpr
  simp only [properChecks, P37.truncations, List.map_append, listAll_eq_all,
    List.all_append, List.all_map, List.all_eq_true, Function.comp_apply, id_eq,
    Bool.and_eq_true]
  constructor
  · intro checks
    constructor
    · intro index member
      have inside := List.mem_range.mp member
      exact (checks (index + 1) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)).1
    · intro index member
      have inside := List.mem_range.mp member
      simpa only [Nat.sub_add_eq] using
        (checks (index + 1) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)).2
  · rintro ⟨left, right⟩ index member
    obtain ⟨lower, upper⟩ := List.mem_range'_1.mp member
    have inside : index - 1 ∈ List.range ((P37.digitsBE n).length - 1) :=
      List.mem_range.mpr (by omega)
    refine ⟨?_, ?_⟩
    · simpa only [Nat.sub_add_cancel lower] using left (index - 1) inside
    · have equal : (P37.digitsBE n).length - (index - 1) - 1 =
          (P37.digitsBE n).length - index := by omega
      simpa only [equal] using right (index - 1) inside

theorem reference_eq_prime_and_proper (n : Nat) :
    P37.isTruncatablePrime n = (P37.isPrime n && properTruncatable n) := by
  by_cases small : n < 10
  · interval_cases n <;> decide +kernel
  · have large : ¬ n ≤ 7 := by omega
    simp only [P37.isTruncatablePrime, if_neg large, properTruncatable, if_neg small,
      properChecks_eq_all]

theorem reference_prime (n : Nat) (accepted : P37.isTruncatablePrime n = true) :
    Nat.Prime n := by
  rw [reference_eq_prime_and_proper, Bool.and_eq_true] at accepted
  exact of_decide_eq_true accepted.1

theorem reference_large (n : Nat) (accepted : P37.isTruncatablePrime n = true) : 10 ≤ n := by
  rw [reference_eq_prime_and_proper, Bool.and_eq_true] at accepted
  by_contra small
  simp [properTruncatable, show n < 10 by omega] at accepted

theorem reference_checks (n : Nat) (accepted : P37.isTruncatablePrime n = true) :
    properChecks n = true := by
  have large := reference_large n accepted
  rw [reference_eq_prime_and_proper, Bool.and_eq_true] at accepted
  simpa [properTruncatable, show ¬ n < 10 by omega] using accepted.2

end ProjectEulerStatements.TruncatablePrimes
