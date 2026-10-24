import ProjectEulerStatements.Lib.MagicRingIndexing
import lang.py.FormalSW.Combinations

/-! Complete inner selections and reconstruction of the forced outer labels. -/
namespace ProjectEulerStatements.MagicRing
open FormalSW.PyAst
set_option Elab.async false

def labels (n : Nat) : List Nat := List.range' 1 (2 * n)

theorem ring_eq {n : Nat} (left right : Ring n)
    (outer : left.outer = right.outer) (inner : left.inner = right.inner) : left = right := by
  cases left
  cases right
  cases outer
  cases inner
  rfl

theorem label_bounds {n : Nat} (ring : Ring n) (value : Nat)
    (member : value ∈ ring.outer ∨ value ∈ ring.inner) : 1 ≤ value ∧ value ≤ 2 * n := by
  have selected : value ∈ List.range' 1 (2 * n) :=
    ring.labels.mem_iff.mp (List.mem_append.mpr member)
  have bounds := List.mem_range'_1.mp selected
  omega

def orderedInner {n : Nat} (ring : Ring n) : List Nat :=
  (labels n).filter (fun value => decide (value ∈ ring.inner))

theorem orderedInner_perm {n : Nat} (ring : Ring n) : (orderedInner ring).Perm ring.inner := by
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_range' (s := 1) (n := 2 * n)).filter _) (inner_nodup ring)).mpr
  intro value
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun member => member.2
  · intro member
    exact ⟨ring.labels.mem_iff.mp (List.mem_append_right _ member), member⟩

theorem orderedInner_combination {n : Nat} (ring : Ring n) :
    orderedInner ring ∈ Combinations.rows n (labels n) := by
  apply (Combinations.mem_rows_iff n (labels n) (orderedInner ring)).mpr
  exact ⟨List.filter_sublist, (orderedInner_perm ring).length_eq.trans ring.inner_length⟩

theorem inner_permutation {n : Nat} (ring : Ring n) :
    ring.inner ∈ Permutations.rows n (orderedInner ring) := by
  have size : (orderedInner ring).length = n :=
    (orderedInner_perm ring).length_eq.trans ring.inner_length
  simpa only [size] using Permutations.mem_rows_full (orderedInner_perm ring).symm

theorem full_assignment {n : Nat} (ring : Ring n) :
    ring.outer ++ ring.inner ∈ Permutations.rows (2 * n) (labels n) := by
  simpa only [labels, List.length_range'] using Permutations.mem_rows_full ring.labels

theorem outer_complement {n : Nat} (ring : Ring n) (value : Nat) :
    value ∈ ring.outer ↔ value ∈ labels n ∧ value ∉ ring.inner := by
  have distinct := ring.labels.symm.nodup (List.nodup_range' (s := 1) (n := 2 * n))
  have separate := (List.nodup_append.mp distinct).2.2
  constructor
  · intro member
    refine ⟨ring.labels.mem_iff.mp (List.mem_append_left _ member), ?_⟩
    intro inside
    exact separate value member value inside rfl
  · rintro ⟨member, absent⟩
    have selected := ring.labels.mem_iff.mpr member
    exact (List.mem_append.mp selected).resolve_right absent

theorem perm_of_complement (n : Nat) (outer inner : List Nat)
    (outerDistinct : outer.Nodup) (innerDistinct : inner.Nodup)
    (innerSubset : ∀ value ∈ inner, value ∈ labels n)
    (complement : ∀ value, value ∈ outer ↔ value ∈ labels n ∧ value ∉ inner) :
    (outer ++ inner).Perm (labels n) := by
  have separate : ∀ a ∈ outer, ∀ b ∈ inner, a ≠ b := by
    intro a member b inside same
    subst b
    exact (complement a).mp member |>.2 inside
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_append.mpr ⟨outerDistinct, innerDistinct, separate⟩) List.nodup_range').mpr
  intro value
  constructor
  · intro member
    rcases List.mem_append.mp member with member | member
    · exact ((complement value).mp member).1
    · exact innerSubset value member
  · intro member
    by_cases inside : value ∈ inner
    · exact List.mem_append_right _ inside
    · exact List.mem_append_left _ ((complement value).mpr ⟨member, inside⟩)

def target (n : Nat) (inner : List Nat) : Nat := (n * (2 * n + 1) + inner.sum) / n
def derivedOuter (n : Nat) (inner : List Nat) : List Nat :=
  (List.range n).map (fun index => target n inner - (inner[index]?).getD 0 -
    (inner[(index + 1) % n]?).getD 0)

theorem derivedOuter_length (n : Nat) (inner : List Nat) : (derivedOuter n inner).length = n := by
  simp [derivedOuter]

theorem derivedOuter_eq {n : Nat} (ring : Ring n) (positive : 0 < n)
    (sum : Nat) (magic : Magic ring sum) : derivedOuter n ring.inner = ring.outer := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < n
  · have inRange : index < (List.range n).length := by simpa using inside
    have outerInside : index < ring.outer.length := by rw [ring.outer_length]; exact inside
    have innerInside : index < ring.inner.length := by rw [ring.inner_length]; exact inside
    have nextInside : (index + 1) % n < ring.inner.length := by
      rw [ring.inner_length]
      exact Nat.mod_lt _ positive
    have inCycle : index < (cycle ring.outer ring.inner).length := by
      rw [cycle_length]
      exact inside
    have forced := forced_outer ring sum magic _ (List.getElem_mem inCycle)
    rw [cycle_getElem ring index inside] at forced
    simp only [derivedOuter, List.getElem?_map, List.getElem?_eq_getElem inRange,
      List.getElem_range, Option.map_some, List.getElem?_eq_getElem outerInside,
      List.getElem?_eq_getElem innerInside, List.getElem?_eq_getElem nextInside, Option.getD_some]
    congr 1
    rw [target, ← target_eq_quotient ring positive sum magic]
    exact forced.symm
  · have rangeEnd : (List.range n)[index]? = none :=
      List.getElem?_eq_none (by simpa using (by omega : n ≤ index))
    have outerEnd : ring.outer[index]? = none :=
      List.getElem?_eq_none (by rw [ring.outer_length]; omega)
    simp only [derivedOuter, List.getElem?_map, rangeEnd, Option.map_none, outerEnd]

theorem derived_magic {n : Nat} (ring : Ring n) (forced : ring.outer = derivedOuter n ring.inner) :
    Magic ring (target n ring.inner) := by
  intro triple member
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp member
  have inN : index < n := by simpa only [cycle_length] using inside
  have inRange : index < (List.range n).length := by simpa using inN
  have outerInside : index < ring.outer.length := by rw [ring.outer_length]; exact inN
  have innerInside : index < ring.inner.length := by rw [ring.inner_length]; exact inN
  have nextInside : (index + 1) % n < ring.inner.length := by
    rw [ring.inner_length]
    exact Nat.mod_lt _ (by omega)
  have positive := (label_bounds ring ring.outer[index] (Or.inl (List.getElem_mem outerInside))).1
  have equation := congrArg (fun values => values[index]?) forced
  simp only [derivedOuter, List.getElem?_map, List.getElem?_eq_getElem inRange,
    List.getElem_range, Option.map_some, List.getElem?_eq_getElem outerInside,
    List.getElem?_eq_getElem innerInside, List.getElem?_eq_getElem nextInside, Option.getD_some,
    Option.some.injEq] at equation
  rw [← same, cycle_getElem ring index inN]
  dsimp only
  omega

theorem orderedInner_width {n : Nat} (ring : Ring n) :
    ((labels n).map digitWidth).sum + ((orderedInner ring).map digitWidth).sum =
      (text ring.outer ring.inner).toList.length := by
  rw [((orderedInner_perm ring).map digitWidth).sum_eq, text_length]
  rfl

end ProjectEulerStatements.MagicRing
