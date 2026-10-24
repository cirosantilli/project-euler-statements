import ProjectEulerStatements.Lib.PandigitalBounds
import ProjectEulerStatements.Lib.PandigitalProducts
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Basic
import Init.Data.List.Nat.Range

/-! Reduce the reference rectangle using decimal-length bounds, retaining every
accepted product. Deduplication makes the final sum independent of row order. -/
namespace ProjectEulerStatements.PandigitalReference
open PandigitalProducts

set_option Elab.async false

/-- The reference predicate evaluated over one optimized factor interval. -/
def referenceRow (lower upper a : Nat) : List Nat :=
  ((List.range' (lowerBound lower a) (upperBound upper a + 1 - lowerBound lower a)).filter
    (P32.pandigitalProduct a)).map (a * ·)

/-- The two factor-length cases, in the same order as the optimized search. -/
def referenceProducts : List Nat :=
  (List.range' 1 9).flatMap (referenceRow 1000 9999) ++
    (List.range' 10 90).flatMap (referenceRow 100 999)

private def chosen (a b : Nat) : List Nat :=
  if a = 0 ∨ b = 0 then [] else if P32.pandigitalProduct a b then [a * b] else []

private def rawProducts (maxA maxB : Nat) : List Nat :=
  (List.range (maxA + 1)).flatMap (fun a => (List.range (maxB + 1)).flatMap (chosen a))

private theorem row_fold (a : Nat) (bs acc : List Nat) :
    bs.foldr (fun b rest => if a = 0 ∨ b = 0 then rest
      else if P32.pandigitalProduct a b then a * b :: rest else rest) acc =
      bs.flatMap (chosen a) ++ acc := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      by_cases zero : a = 0 ∨ b = 0 <;> cases accepted : P32.pandigitalProduct a b <;>
        simp [chosen, zero, accepted, ih]

private theorem naive_eq_raw (maxA maxB : Nat) :
    P32.naive maxA maxB = (rawProducts maxA maxB).eraseDups.sum := by
  have enumerate (as : List Nat) :
      as.foldr (fun a acc => (List.range (maxB + 1)).foldr
        (fun b rest => if a = 0 ∨ b = 0 then rest
          else if P32.pandigitalProduct a b then a * b :: rest else rest) acc) [] =
      as.flatMap (fun a => (List.range (maxB + 1)).flatMap (chosen a)) := by
    induction as with
    | nil => rfl
    | cons a as ih => rw [List.foldr_cons, row_fold, ih, List.flatMap_cons]
  simp only [P32.naive, P32.sumPandigitalProducts, enumerate]
  rw [← List.sum_eq_foldl]
  rfl

private theorem mem_raw (maxA maxB value : Nat) :
    value ∈ rawProducts maxA maxB ↔
      ∃ a b, 1 ≤ a ∧ a ≤ maxA ∧ 1 ≤ b ∧ b ≤ maxB ∧
        P32.pandigitalProduct a b = true ∧ value = a * b := by
  simp only [rawProducts, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, aBound, b, bBound, present⟩
    by_cases zero : a = 0 ∨ b = 0
    · simp [chosen, zero] at present
    · by_cases accepted : P32.pandigitalProduct a b = true
      · have equal : value = a * b := by simpa [chosen, zero, accepted] using present
        exact ⟨a, b, by omega, by omega, by omega, by omega, accepted, equal⟩
      · simp [chosen, zero, accepted] at present
  · rintro ⟨a, b, aPositive, aBound, bPositive, bBound, accepted, equal⟩
    refine ⟨a, by omega, b, by omega, ?_⟩
    simp [chosen, show ¬(a = 0 ∨ b = 0) by omega, accepted, equal]

private theorem lower_iff (lower a b : Nat) (positive : 0 < a) :
    lowerBound lower a ≤ b ↔ lower ≤ b ∧ 1000 ≤ a * b := by
  rw [lowerBound, Nat.max_le, Nat.div_le_iff_le_mul positive]
  rw [Nat.mul_comm b a]
  omega

private theorem upper_iff (upper a b : Nat) (positive : 0 < a) :
    b ≤ upperBound upper a ↔ b ≤ upper ∧ a * b ≤ 9999 := by
  rw [upperBound, Nat.le_min, Nat.le_div_iff_mul_le positive, Nat.mul_comm b a]

private theorem mem_row (lower upper a value : Nat) (positive : 0 < a) :
    value ∈ referenceRow lower upper a ↔
      ∃ b, lower ≤ b ∧ b ≤ upper ∧ 1000 ≤ a * b ∧ a * b ≤ 9999 ∧
        P32.pandigitalProduct a b = true ∧ value = a * b := by
  simp only [referenceRow, List.mem_map, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨b, ⟨⟨start, stop⟩, accepted⟩, equal⟩
    have upperBounded : b ≤ upperBound upper a := by omega
    have lowerFacts := (lower_iff lower a b positive).mp start
    have upperFacts := (upper_iff upper a b positive).mp upperBounded
    exact ⟨b, lowerFacts.1, upperFacts.1, lowerFacts.2, upperFacts.2, accepted, equal.symm⟩
  · rintro ⟨b, lower, upper, productLower, productUpper, accepted, equal⟩
    have start := (lower_iff _ a b positive).mpr ⟨lower, productLower⟩
    have stop := (upper_iff _ a b positive).mpr ⟨upper, productUpper⟩
    exact ⟨b, ⟨⟨start, by omega⟩, accepted⟩, equal.symm⟩

/-- Every accepted product in the original rectangle occurs in the bounded rows,
and every product in those rows belongs to the original rectangle. -/
theorem product_membership (value : Nat) :
    value ∈ rawProducts 99 9999 ↔ value ∈ referenceProducts := by
  constructor
  · intro member
    obtain ⟨a, b, aPositive, aBound, bPositive, bBound, accepted, equal⟩ := (mem_raw 99 9999 value).mp member
    have bounds := PandigitalBounds.reference_bounds a b aPositive aBound bPositive bBound accepted
    simp only [referenceProducts, List.mem_append, List.mem_flatMap]
    by_cases oneDigit : a < 10
    · left
      refine ⟨a, ?_, (mem_row 1000 9999 a value (by omega)).mpr ?_⟩
      · simp only [List.mem_range'_1]
        omega
      · have factors : 1000 ≤ b ∧ b ≤ 9999 := by simpa only [if_pos oneDigit] using bounds.2
        exact ⟨b, factors.1, factors.2, bounds.1.1, bounds.1.2, accepted, equal⟩
    · right
      refine ⟨a, ?_, (mem_row 100 999 a value (by omega)).mpr ?_⟩
      · simp only [List.mem_range'_1]
        omega
      · have factors : 100 ≤ b ∧ b ≤ 999 := by simpa only [if_neg oneDigit] using bounds.2
        exact ⟨b, factors.1, factors.2, bounds.1.1, bounds.1.2, accepted, equal⟩
  · intro member
    simp only [referenceProducts, List.mem_append, List.mem_flatMap] at member
    rcases member with ⟨a, aMember, rowMember⟩ | ⟨a, aMember, rowMember⟩
    · have aBounds := List.mem_range'_1.mp aMember
      obtain ⟨b, lower, upper, _, _, accepted, equal⟩ := (mem_row 1000 9999 a value (by omega)).mp rowMember
      exact (mem_raw 99 9999 value).mpr ⟨a, b, by omega, by omega, by omega, upper, accepted, equal⟩
    · have aBounds := List.mem_range'_1.mp aMember
      obtain ⟨b, lower, upper, _, _, accepted, equal⟩ := (mem_row 100 999 a value (by omega)).mp rowMember
      exact (mem_raw 99 9999 value).mpr ⟨a, b, by omega, by omega, by omega, by omega, accepted, equal⟩

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
          · exact ih _ (by have := List.length_filter_le (fun n => !(n == head)) tail; simp only [List.length_cons] at measure; omega)
              (tail.filter (fun n => !(n == head))) rfl

private theorem sum_perm {left right : List Nat} (permutation : left.Perm right) : left.sum = right.sum := by
  induction permutation with
  | nil => rfl
  | cons head permutation ih => simpa only [List.sum_cons] using congrArg (Nat.add head) ih
  | swap a b tail => simp only [List.sum_cons]; omega
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Arithmetic range reduction of the exact reference function, with no evaluated
certificate and no assumption about digit-mask correctness. -/
theorem naive_eq_referenceProducts : P32.naive 99 9999 = referenceProducts.eraseDups.sum := by
  rw [naive_eq_raw]
  apply sum_perm
  apply (List.perm_ext_iff_of_nodup (eraseDups_nodup _) (eraseDups_nodup _)).mpr
  intro value
  simpa only [List.mem_eraseDups] using product_membership value

end ProjectEulerStatements.PandigitalReference
