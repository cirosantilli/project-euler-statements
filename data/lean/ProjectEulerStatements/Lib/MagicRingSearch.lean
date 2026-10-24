import ProjectEulerStatements.Lib.MagicRingCandidates
import ProjectEulerStatements.Lib.ListMaximum
import Mathlib.Data.String.Basic

/-! The exhaustive assignments and forced-outer search produce the same canonical candidates. -/
namespace ProjectEulerStatements.MagicRing
open FormalSW.PyAst
set_option Elab.async false

def pack (n : Nat) (outer inner : List Nat) : Option (Ring n) :=
  if outerSize : outer.length = n then
    if innerSize : inner.length = n then
      if assignment : (outer ++ inner).Perm (labels n) then
        some ⟨outer, inner, outerSize, innerSize, assignment⟩
      else none
    else none
  else none

theorem pack_self {n : Nat} (ring : Ring n) : pack n ring.outer ring.inner = some ring := by
  have complete : (ring.outer ++ ring.inner).Perm (labels n) := ring.labels
  simp only [pack, dif_pos ring.outer_length, dif_pos ring.inner_length, dif_pos complete]

theorem pack_spec {n : Nat} (outer inner : List Nat) (ring : Ring n) :
    pack n outer inner = some ring ↔ ring.outer = outer ∧ ring.inner = inner := by
  constructor
  · intro packed
    unfold pack at packed
    split at packed <;> try contradiction
    split at packed <;> try contradiction
    split at packed <;> try contradiction
    cases packed
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact pack_self ring

def referenceRings (n : Nat) : List (Ring n) :=
  (Permutations.rows (2 * n) (labels n)).filterMap (fun assignment =>
    pack n (assignment.take n) (assignment.drop n))

theorem mem_referenceRings {n : Nat} (ring : Ring n) : ring ∈ referenceRings n := by
  have splitFirst : (ring.outer ++ ring.inner).take n = ring.outer := by
    simpa only [ring.outer_length] using List.take_left (l₁ := ring.outer) (l₂ := ring.inner)
  have splitLast : (ring.outer ++ ring.inner).drop n = ring.inner := by
    simpa only [ring.outer_length] using List.drop_left (l₁ := ring.outer) (l₂ := ring.inner)
  apply List.mem_filterMap.mpr
  exact ⟨ring.outer ++ ring.inner, full_assignment ring, by rw [splitFirst, splitLast, pack_self]⟩

def optimizedRings (n : Nat) : List (Ring n) :=
  (Combinations.rows n (labels n)).flatMap (fun selected =>
    (Permutations.rows n selected).filterMap (fun inner => pack n (derivedOuter n inner) inner))

theorem mem_optimizedRings {n : Nat} (ring : Ring n) :
    ring ∈ optimizedRings n ↔ ring.outer = derivedOuter n ring.inner := by
  constructor
  · intro member
    obtain ⟨selected, _, chosen⟩ := List.mem_flatMap.mp member
    obtain ⟨inner, _, packed⟩ := List.mem_filterMap.mp chosen
    have shape := (pack_spec _ _ ring).mp packed
    rw [shape.2]
    exact shape.1
  · intro forced
    apply List.mem_flatMap.mpr
    refine ⟨orderedInner ring, orderedInner_combination ring, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨ring.inner, inner_permutation ring, by rw [← forced]; exact pack_self ring⟩

theorem optimizedRings_complete {n : Nat} (ring : Ring n) (positive : 0 < n) :
    ring ∈ optimizedRings n ↔ ∃ sum, Magic ring sum := by
  rw [mem_optimizedRings]
  constructor
  · intro forced
    exact ⟨target n ring.inner, derived_magic ring forced⟩
  · rintro ⟨sum, magic⟩
    exact (derivedOuter_eq ring positive sum magic).symm

def firstSum {n : Nat} (ring : Ring n) : Nat :=
  ring.outer.headD 0 + ring.inner.headD 0 + (ring.inner[1]?).getD 0

theorem firstSum_eq {n : Nat} (ring : Ring n) (size : 2 ≤ n) (sum : Nat) (magic : Magic ring sum) :
    firstSum ring = sum := by
  have inCycle : 0 < (cycle ring.outer ring.inner).length := by rw [cycle_length]; omega
  have first := magic _ (List.getElem_mem inCycle)
  rw [cycle_getElem ring 0 (by omega)] at first
  have outerFirst : ring.outer.headD 0 = ring.outer[0]'(by rw [ring.outer_length]; omega) := by
    simp only [List.headD_eq_head?_getD, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < ring.outer.length by rw [ring.outer_length]; omega),
      Option.getD_some]
  have innerFirst : ring.inner.headD 0 = ring.inner[0]'(by rw [ring.inner_length]; omega) := by
    simp only [List.headD_eq_head?_getD, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < ring.inner.length by rw [ring.inner_length]; omega),
      Option.getD_some]
  simpa only [firstSum, outerFirst, innerFirst, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n),
    List.getElem?_eq_getElem (show 1 < ring.inner.length by rw [ring.inner_length]; omega),
    Option.getD_some] using first

instance {n : Nat} (ring : Ring n) (sum : Nat) : Decidable (Magic ring sum) := by
  unfold Magic
  infer_instance

instance {n : Nat} (ring : Ring n) : Decidable (Canonical ring) := by
  unfold Canonical
  infer_instance

theorem magic_firstSum_iff {n : Nat} (ring : Ring n) (size : 2 ≤ n) :
    Magic ring (firstSum ring) ↔ ∃ sum, Magic ring sum := by
  constructor
  · exact fun magic => ⟨firstSum ring, magic⟩
  · rintro ⟨sum, magic⟩
    simpa only [firstSum_eq ring size sum magic] using magic

def referenceValues (n digits : Nat) : List String :=
  (referenceRings n).filterMap (fun ring =>
    if Canonical ring ∧ Magic ring (firstSum ring) ∧
        (text ring.outer ring.inner).toList.length = digits
    then some (text ring.outer ring.inner) else none)

def optimizedValues (n digits : Nat) : List String :=
  (optimizedRings n).filterMap (fun ring =>
    let canonical := ring.canonicalize
    if (text canonical.outer canonical.inner).toList.length = digits
    then some (text canonical.outer canonical.inner) else none)

def Result (n digits : Nat) (value : String) : Prop :=
  ∃ ring : Ring n, Canonical ring ∧ (∃ sum, Magic ring sum) ∧
    (text ring.outer ring.inner).toList.length = digits ∧ value = text ring.outer ring.inner

theorem mem_referenceValues (n digits : Nat) (value : String) (size : 2 ≤ n) :
    value ∈ referenceValues n digits ↔ Result n digits value := by
  constructor
  · intro member
    obtain ⟨ring, _, output⟩ := List.mem_filterMap.mp member
    split_ifs at output with accepted
    exact ⟨ring, accepted.1, ⟨firstSum ring, accepted.2.1⟩, accepted.2.2,
      (Option.some.inj output).symm⟩
  · rintro ⟨ring, canonical, magic, length, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨ring, mem_referenceRings ring, ?_⟩
    simp only [canonical, (magic_firstSum_iff ring size).mpr magic, length, and_self, if_true]

theorem mem_optimizedValues (n digits : Nat) (value : String) (positive : 0 < n) :
    value ∈ optimizedValues n digits ↔ Result n digits value := by
  constructor
  · intro member
    obtain ⟨ring, selected, output⟩ := List.mem_filterMap.mp member
    change (if (text ring.canonicalize.outer ring.canonicalize.inner).toList.length = digits then
      some (text ring.canonicalize.outer ring.canonicalize.inner) else none) = some value at output
    split_ifs at output with length
    obtain ⟨sum, magic⟩ := (optimizedRings_complete ring positive).mp selected
    exact ⟨ring.canonicalize, canonicalize_canonical ring positive,
      ⟨sum, canonicalize_magic ring sum magic⟩, length, (Option.some.inj output).symm⟩
  · rintro ⟨ring, canonical, magic, length, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨ring, (optimizedRings_complete ring positive).mpr magic, ?_⟩
    simp only [canonicalize_fixed ring positive canonical, length, if_true]

def referenceAnswer (n digits : Nat) : String := (referenceValues n digits).foldl max ""
def optimizedAnswer (n digits : Nat) : String := (optimizedValues n digits).foldl max ""

theorem answers_equal (n digits : Nat) (size : 2 ≤ n) :
    optimizedAnswer n digits = referenceAnswer n digits := by
  apply ListMaximum.eq_of_same_members
  intro value
  rw [mem_optimizedValues n digits value (by omega), mem_referenceValues n digits value size]

end ProjectEulerStatements.MagicRing
