import ProjectEulerStatements.Lib.HeapqBottomUp
import lang.py.FormalSW.HeapqTotal

/-! Coverage and local ordering of the concrete heapify traversal. Cache traversal
starts from the internal tree's leaves and follows left-child links towards the
root; its starting ranges jointly cover every such leaf. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
set_option Elab.async false

theorem mem_parentPath_self (position : Nat) : position ∈ Heapq.parentPath position := by
  rw [Heapq.parentPath]
  exact List.mem_cons_self

theorem mem_parentPath_trans (first middle last : Nat)
    (initial : middle ∈ Heapq.parentPath first) (final : last ∈ Heapq.parentPath middle) :
    last ∈ Heapq.parentPath first := by
  rw [Heapq.parentPath] at initial ⊢
  rcases List.mem_cons.mp initial with same | tail
  · subst middle
    rw [Heapq.parentPath] at final
    exact final
  · apply List.mem_cons_of_mem
    by_cases odd : first % 2 = 1
    · rw [if_pos odd] at tail ⊢
      exact mem_parentPath_trans (first / 2) middle last tail final
    · simp [odd] at tail
termination_by first
decreasing_by apply Nat.div_lt_self <;> omega

/-- Every internal node lies on the parent path of a leaf of the internal tree. -/
theorem exists_parentPath_leaf (size position : Nat) (inside : position < size) :
    ∃ leaf, size / 2 ≤ leaf ∧ leaf < size ∧ position ∈ Heapq.parentPath leaf := by
  by_cases bottom : size / 2 ≤ position
  · exact ⟨position, bottom, inside, mem_parentPath_self position⟩
  · have childInside : 2 * position + 1 < size := by omega
    obtain ⟨leaf, lower, upper, visited⟩ :=
      exists_parentPath_leaf size (2 * position + 1) childInside
    have parentVisited : position ∈ Heapq.parentPath (2 * position + 1) := by
      rw [Heapq.parentPath]
      apply List.mem_cons_of_mem
      rw [if_pos (by omega)]
      have parent : (2 * position + 1) / 2 = position := by omega
      rw [parent]
      exact mem_parentPath_self position
    exact ⟨leaf, lower, upper, mem_parentPath_trans leaf (2 * position + 1) position
      visited parentVisited⟩
termination_by size - position
decreasing_by omega

theorem mem_descending_iff (start count index : Nat) :
    index ∈ Heapq.descending start count ↔ start ≤ index ∧ index < start + count := by
  constructor
  · exact Heapq.mem_descending_bounds start count index
  · intro bounds
    simp only [Heapq.descending, List.mem_map, List.mem_reverse, List.mem_range]
    exact ⟨index - start, by omega, by omega⟩

/-- The split point changes traversal order, but all internal-tree leaves remain covered. -/
theorem mem_cache_starts (size split leaf : Nat) (splitBound : split ≤ size)
    (lower : size / 2 ≤ leaf) (upper : leaf < size) :
    leaf ∈ Heapq.descending (size / 2) (split - size / 2) ++
      Heapq.descending split (size - split) := by
  by_cases first : leaf < split
  · apply List.mem_append_left
    exact (mem_descending_iff _ _ _).mpr ⟨lower, by omega⟩
  · apply List.mem_append_right
    exact (mem_descending_iff _ _ _).mpr ⟨by omega, by omega⟩

/-- Both runtime strategies cover every internal node, without a list-length bound. -/
theorem heapifyOrder_complete (size index : Nat) :
    index ∈ Heapq.heapifyOrder size ↔ index < size / 2 := by
  constructor
  · exact Heapq.heapifyOrder_internal size index
  · intro inside
    by_cases cached : size > 2500
    · rw [Heapq.heapifyOrder, if_pos cached]
      obtain ⟨leaf, lower, upper, visited⟩ := exists_parentPath_leaf (size / 2) index inside
      have splitBound : 2 ^ Nat.log2 (size / 2 + 1) - 1 ≤ size / 2 := by
        have : 2 ^ Nat.log2 (size / 2 + 1) ≤ size / 2 + 1 :=
          Nat.log2_self_le (by omega)
        omega
      exact List.mem_flatMap.mpr ⟨leaf, mem_cache_starts _ _ _ splitBound lower upper, visited⟩
    · simpa [Heapq.heapifyOrder, cached] using inside

theorem BottomUp.parentPath (position : Nat) : BottomUp (Heapq.parentPath position) := by
  unfold BottomUp
  rw [Heapq.parentPath, List.pairwise_cons]
  by_cases odd : position % 2 = 1
  · rw [if_pos odd]
    constructor
    · intro later member below
      have upper := Heapq.mem_parentPath_le (position / 2) later member
      have lower := below.le
      omega
    · exact BottomUp.parentPath (position / 2)
  · simp [odd]
termination_by position
decreasing_by apply Nat.div_lt_self <;> omega

theorem heapifyOrder_bottomUp_uncached (size : Nat) (uncached : ¬size > 2500) :
    BottomUp (Heapq.heapifyOrder size) := by
  rw [Heapq.heapifyOrder, if_neg uncached]
  exact BottomUp.reverse_range _

/-- Once the concrete traversal is bottom-up, its coverage supplies the full heapify result. -/
theorem heapify_ordered_of_bottomUp {α : Type*} [LinearOrder α]
    (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address : Nat) (values : List α)
    (found : heap[address]? = some (.list (values.map encode)))
    (traversal : BottomUp (Heapq.heapifyOrder values.length)) :
    ∃ changed, Heapq.heapify [.ref address] heap =
        some (.ok (.scalar .none), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed := by
  obtain ⟨changed, finished, contents, ordered⟩ := siftAll_ordered_of_complete encode comparison
    heap address values (Heapq.heapifyOrder values.length) found traversal
    (heapifyOrder_complete values.length)
  refine ⟨changed, ?_, contents, ordered⟩
  apply Heapq.heapify_result heap _ address (values.map encode) (.ok ()) found
  simpa only [List.length_map] using finished

end ProjectEulerStatements.MinHeap
