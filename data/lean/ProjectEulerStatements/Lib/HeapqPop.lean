import ProjectEulerStatements.Lib.MinHeapSink
import ProjectEulerStatements.Lib.HeapqPush

/-! Ordering guarantees for concrete heap pops. The downward sift selects the
smaller child, including the runtime's right-child tie break, before the upward
repair. All swaps preserve the caller's other heap objects. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

theorem siftChildren_root_ordered (encode : α → Mutable.Value)
    (comparison : EncodesOrder encode) (heap : Mutable.Heap)
    (address size position : Nat) (values : List α)
    (sized : size = values.length) (inside : position < size)
    (sinking : Sinking values position)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.siftChildren address size 0 position heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have positionInside : position < values.length := by omega
  have descend (child : Nat) (childInside : child < size) (edge : Child position child)
      (least : ∀ other (ho : other < values.length),
        Child position other → values[child]'(by omega) ≤ values[other]) :
      ∃ changed, (do
          Heapq.swap address position child
          Heapq.siftChildren address size 0 child) heap =
          some (.ok (), heap.set address (.list (changed.map encode))) ∧
        changed.Perm values ∧ Ordered changed := by
    have bounded : child < values.length := by omega
    have before := edge.increasing
    let exchanged := (values.set position values[child]).set child values[position]
    have permutation : exchanged.Perm values :=
      Heapq.swap_contents_perm values position child positionInside bounded
    have newSinking : Sinking exchanged child :=
      sinking.swap values position child positionInside bounded edge least
    obtain ⟨changed, finished, contents, ordered⟩ := siftChildren_root_ordered encode comparison
      (heap.set address (.list (exchanged.map encode))) address size child exchanged
      (by rw [permutation.length_eq]; exact sized) childInside newSinking (by simp [valid])
    simp [exchanged] at finished
    refine ⟨changed, ?_, contents.trans permutation, ordered⟩
    simp [Heapq.swap_mapped_list encode heap address position child values found positionInside
      bounded, finished]
  by_cases leftInside : 2 * position + 1 < size
  · have leftBounded : 2 * position + 1 < values.length := by omega
    have leftEdge : Child position (2 * position + 1) := Or.inl rfl
    by_cases rightInside : 2 * position + 2 < size
    · have rightBounded : 2 * position + 2 < values.length := by omega
      have rightEdge : Child position (2 * position + 2) := Or.inr rfl
      have readLeft : Heapq.atIndex address (2 * position + 1) heap =
          some (.ok (encode values[2 * position + 1]), heap) := by
        rw [Heapq.atIndex_list heap address (2 * position + 1) (values.map encode) found
          (by simpa), List.getElem_map encode]
      have readRight : Heapq.atIndex address (2 * position + 2) heap =
          some (.ok (encode values[2 * position + 2]), heap) := by
        rw [Heapq.atIndex_list heap address (2 * position + 2) (values.map encode) found
          (by simpa), List.getElem_map encode]
      have compared := comparison heap values[2 * position + 1] values[2 * position + 2]
      by_cases less : values[2 * position + 1] < values[2 * position + 2]
      · have least : ∀ other (ho : other < values.length),
            Child position other → values[2 * position + 1] ≤ values[other] := by
          intro other ho linked
          rcases linked with rfl | rfl
          · exact le_rfl
          · exact less.le
        obtain ⟨changed, finished, contents, ordered⟩ :=
          descend (2 * position + 1) leftInside leftEdge least
        refine ⟨changed, ?_, contents, ordered⟩
        rw [Heapq.siftChildren]
        simpa [leftInside, rightInside, readLeft, readRight, compared, less,
          Nat.add_assoc] using finished
      · have least : ∀ other (ho : other < values.length),
            Child position other → values[2 * position + 2] ≤ values[other] := by
          intro other ho linked
          rcases linked with rfl | rfl
          · exact le_of_not_gt less
          · exact le_rfl
        obtain ⟨changed, finished, contents, ordered⟩ :=
          descend (2 * position + 2) rightInside rightEdge least
        refine ⟨changed, ?_, contents, ordered⟩
        rw [Heapq.siftChildren]
        simpa [leftInside, rightInside, readLeft, readRight, compared, less,
          Nat.add_assoc] using finished
    · have least : ∀ other (ho : other < values.length),
          Child position other → values[2 * position + 1] ≤ values[other] := by
        intro other ho linked
        have same : other = 2 * position + 1 := by unfold Child at linked; omega
        subst other
        exact le_rfl
      obtain ⟨changed, finished, contents, ordered⟩ :=
        descend (2 * position + 1) leftInside leftEdge least
      refine ⟨changed, ?_, contents, ordered⟩
      rw [Heapq.siftChildren]
      simpa [leftInside, rightInside, Nat.add_assoc] using finished
  · obtain ⟨changed, finished, contents, ordered⟩ := siftDown_root_ordered encode comparison
      heap address position values positionInside (sinking.leaf values position (by omega)) found
    exact ⟨changed, by rw [Heapq.siftChildren]; simpa [leftInside] using finished,
      contents, ordered⟩
termination_by size - position
decreasing_by omega

theorem siftUp_root_ordered (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address : Nat) (values : List α)
    (nonempty : 0 < values.length) (sinking : Sinking values 0)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.siftUp address 0 heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed := by
  obtain ⟨changed, finished, contents, ordered⟩ := siftChildren_root_ordered encode comparison
    heap address values.length 0 values rfl nonempty sinking found
  exact ⟨changed, by simpa [Heapq.siftUp, Heapq.items_list heap address _ found, nonempty]
    using finished, contents, ordered⟩

/-- A nonempty ordered heap returns its root and leaves an ordered permutation of its tail. -/
theorem heappop_ordered (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address : Nat) (root : α) (rest : List α)
    (ordered : Ordered (root :: rest))
    (found : heap[address]? = some (.list ((root :: rest).map encode))) :
    ∃ changed, Heapq.heappop [.ref address] heap =
        some (.ok (encode root), heap.set address (.list (changed.map encode))) ∧
      changed.Perm rest ∧ Ordered changed := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  rcases List.eq_nil_or_concat rest with empty | ⟨middle, last, equation⟩
  · subst rest
    refine ⟨[], ?_, .refl _, ?_⟩
    · exact Heapq.heappop_singleton heap address (encode root) found
    · intro parent hp
      simp at hp
  · have tail : rest = middle ++ [last] := by simpa only [List.concat_eq_append] using equation
    clear equation
    subst rest
    have prefixOrdered : Ordered (root :: middle) :=
      Ordered.prefix (root :: middle) [last] ordered
    obtain ⟨changed, finished, contents, resultOrdered⟩ := siftUp_root_ordered encode comparison
      (heap.set address (.list ((last :: middle).map encode))) address (last :: middle)
      (by simp) (Sinking.replace_root root last middle prefixOrdered) (by simp [valid])
    refine ⟨changed, ?_, contents.trans (List.perm_append_comm (l₁ := [last]) (l₂ := middle)),
      resultOrdered⟩
    rw [Heapq.heappop_nontrivial heap address (encode root) (encode last) (middle.map encode)
      (by simpa using found)]
    simp only [List.map_cons] at finished
    simp [Mutable.eval_map, finished, Except.map]

end ProjectEulerStatements.MinHeap
