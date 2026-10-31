import ProjectEulerStatements.Lib.HeapqLevels

/-! Both concrete heapify traversals are bottom-up. The cache traversal visits
shallow leaves right-to-left, then deeper leaves right-to-left; each leaf's
left-child ancestor path can therefore be repaired immediately after that leaf. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
set_option Elab.async false

theorem descending_strict (start count : Nat) :
    (Heapq.descending start count).Pairwise (fun earlier later => later < earlier) := by
  unfold Heapq.descending
  apply List.pairwise_map.mpr
  apply List.pairwise_reverse.mpr
  have increasing : (List.range count).Pairwise (· < ·) := by
    simpa only [List.range_eq_range'] using (List.pairwise_lt_range' (s := 0) (n := count))
  exact increasing.imp (by intro earlier later smaller; omega)

theorem cacheOrder_bottomUp (size : Nat) :
    BottomUp ((Heapq.descending (size / 2) (2 ^ (size + 1).log2 - 1 - size / 2) ++
      Heapq.descending (2 ^ (size + 1).log2 - 1)
        (size - (2 ^ (size + 1).log2 - 1))).flatMap Heapq.parentPath) := by
  by_cases zero : size = 0
  · subst size
    change List.Pairwise _ []
    exact .nil
  · let level := (size + 1).log2
    let split := 2 ^ level - 1
    have positive : 0 < level := by
      have lower : 2 ^ 1 ≤ size + 1 := by omega
      have := (Nat.le_log2 (show size + 1 ≠ 0 by omega)).mpr lower
      exact this
    have lower : 2 ^ level ≤ size + 1 := Nat.log2_self_le (by omega)
    have upper : size + 1 < 2 ^ (level + 1) := Nat.lt_log2_self
    have splitBound : split ≤ size := by dsimp [split]; omega
    have previous : level - 1 + 1 = level := by omega
    have power : 2 ^ level = 2 ^ (level - 1) * 2 := by
      conv => lhs; rw [← previous]
      rw [Nat.pow_succ]
    have firstLevel : ∀ index ∈ Heapq.descending (size / 2) (split - size / 2),
        depth index = level - 1 := by
      intro index member
      have bounds := Heapq.mem_descending_bounds _ _ _ member
      apply (Nat.log2_eq_iff (by omega)).mpr
      constructor
      · rw [power] at lower
        omega
      · rw [previous]
        dsimp [split] at bounds
        omega
    have secondLevel : ∀ index ∈ Heapq.descending split (size - split),
        depth index = level := by
      intro index member
      have bounds := Heapq.mem_descending_bounds _ _ _ member
      apply (Nat.log2_eq_iff (by omega)).mpr
      constructor
      · dsimp [split] at bounds
        omega
      · omega
    apply List.pairwise_flatMap.mpr
    constructor
    · intro leaf _
      exact BottomUp.parentPath leaf
    · apply List.pairwise_append.mpr
      refine ⟨?_, ?_, ?_⟩
      · apply (descending_strict (size / 2) (split - size / 2)).imp_of_mem
        intro first second firstMember secondMember before
        apply parentPaths_same_level first second
        · rw [firstLevel first firstMember, firstLevel second secondMember]
        · exact before
      · apply (descending_strict split (size - split)).imp_of_mem
        intro first second firstMember secondMember before
        apply parentPaths_same_level first second
        · rw [secondLevel first firstMember, secondLevel second secondMember]
        · exact before
      · intro first firstMember second secondMember
        apply parentPaths_next_level first second
        · rw [firstLevel first firstMember, secondLevel second secondMember]
          omega
        · have firstBounds := Heapq.mem_descending_bounds _ _ _ firstMember
          have secondBounds := Heapq.mem_descending_bounds _ _ _ secondMember
          omega

theorem heapifyOrder_bottomUp (size : Nat) : BottomUp (Heapq.heapifyOrder size) := by
  by_cases cached : size > 2500
  · rw [Heapq.heapifyOrder, if_pos cached]
    exact cacheOrder_bottomUp (size / 2)
  · exact heapifyOrder_bottomUp_uncached size cached

/-- Concrete heapify succeeds and orders a permutation of every input list. -/
theorem heapify_ordered {α : Type*} [LinearOrder α]
    (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address : Nat) (values : List α)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.heapify [.ref address] heap =
        some (.ok (.scalar .none), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed :=
  heapify_ordered_of_bottomUp encode comparison heap address values found
    (heapifyOrder_bottomUp values.length)

end ProjectEulerStatements.MinHeap
