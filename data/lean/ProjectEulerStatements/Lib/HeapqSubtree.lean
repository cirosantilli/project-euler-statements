import ProjectEulerStatements.Lib.MinHeapSubtree
import ProjectEulerStatements.Lib.HeapqPush

/-! Concrete sifting at any subtree root. Ordered child subtrees suffice to
repair the whole subtree; entries outside it retain their original positions. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

theorem siftDown_orderedBelow (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address root position : Nat) (values : List α)
    (inside : position < values.length) (below : Descendant root position)
    (rising : RisingBelow root values position)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.siftDown address root position heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ OrderedBelow root changed ∧ UnchangedOutside root values changed := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have unchanged : heap.set address (.list (values.map encode)) = heap := by
    obtain ⟨bounded, entry⟩ := List.getElem?_eq_some_iff.mp found
    rw [← entry, List.set_getElem_self bounded]
  by_cases atRoot : position = root
  · subst position
    exact ⟨values, by simpa [unchanged] using Heapq.siftDown_stop heap address root root (by omega),
      .refl _, rising.root root values, .refl root values⟩
  · have lower := below.le
    have positive : root < position := by omega
    let parent := (position - 1) / 2
    have smaller : parent < position := by
      have := Nat.div_le_self (position - 1) 2
      dsimp [parent]
      omega
    have parentInside := Nat.lt_trans smaller inside
    have edge : Child parent position := by unfold Child; dsimp [parent]; omega
    have parentBelow := below.parent atRoot edge
    have readValue : Heapq.atIndex address position heap =
        some (.ok (encode values[position]), heap) := by
      rw [Heapq.atIndex_list heap address position (values.map encode) found (by simpa)]
      rw [List.getElem_map encode]
    have readParent : Heapq.atIndex address parent heap =
        some (.ok (encode values[parent]), heap) := by
      rw [Heapq.atIndex_list heap address parent (values.map encode) found (by simpa)]
      rw [List.getElem_map encode]
    have compared := comparison heap values[position] values[parent]
    by_cases less : values[position] < values[parent]
    · let exchanged := (values.set position values[parent]).set parent values[position]
      have permutation : exchanged.Perm values :=
        Heapq.swap_contents_perm values position parent inside parentInside
      have newRising : RisingBelow root exchanged parent :=
        rising.swap root values position parent inside parentInside parentBelow edge less
      obtain ⟨changed, finished, contents, ordered, outside⟩ :=
        siftDown_orderedBelow encode comparison
        (heap.set address (.list (exchanged.map encode))) address root parent exchanged
        (by rw [permutation.length_eq]; exact parentInside) parentBelow newRising (by simp [valid])
      simp [exchanged, parent] at finished
      refine ⟨changed, ?_, contents.trans permutation, ordered,
        (UnchangedOutside.swap root values position parent inside parentInside
          below parentBelow).trans outside⟩
      rw [Heapq.siftDown]
      simp [positive, readValue, readParent, compared, less,
        Heapq.swap_mapped_list encode heap address position parent values found inside parentInside,
        finished, parent]
    · refine ⟨values, ?_, .refl _, rising.settled root values position parent inside parentInside
        edge (le_of_not_gt less), .refl root values⟩
      rw [unchanged, Heapq.siftDown]
      simp [positive, readValue, readParent, compared, less, parent]
termination_by position
decreasing_by exact smaller

theorem siftChildren_orderedBelow (encode : α → Mutable.Value)
    (comparison : EncodesOrder encode) (heap : Mutable.Heap)
    (address size root position : Nat) (values : List α)
    (sized : size = values.length) (inside : position < size)
    (below : Descendant root position) (sinking : SinkingBelow root values position)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.siftChildren address size root position heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ OrderedBelow root changed ∧ UnchangedOutside root values changed := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have positionInside : position < values.length := by omega
  have descend (child : Nat) (childInside : child < size) (edge : Child position child)
      (least : ∀ other (ho : other < values.length),
        Child position other → values[child]'(by omega) ≤ values[other]) :
      ∃ changed, (do
          Heapq.swap address position child
          Heapq.siftChildren address size root child) heap =
          some (.ok (), heap.set address (.list (changed.map encode))) ∧
        changed.Perm values ∧ OrderedBelow root changed ∧ UnchangedOutside root values changed := by
    have bounded : child < values.length := by omega
    have before := edge.increasing
    let exchanged := (values.set position values[child]).set child values[position]
    have permutation : exchanged.Perm values :=
      Heapq.swap_contents_perm values position child positionInside bounded
    have newSinking : SinkingBelow root exchanged child :=
      sinking.swap root values position child positionInside bounded below edge least
    obtain ⟨changed, finished, contents, ordered, outside⟩ :=
      siftChildren_orderedBelow encode comparison
      (heap.set address (.list (exchanged.map encode))) address size root child exchanged
      (by rw [permutation.length_eq]; exact sized) childInside (below.child edge)
      newSinking (by simp [valid])
    simp [exchanged] at finished
    refine ⟨changed, ?_, contents.trans permutation, ordered,
      (UnchangedOutside.swap root values position child positionInside bounded below
        (below.child edge)).trans outside⟩
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
        obtain ⟨changed, finished, contents, ordered, outside⟩ :=
          descend (2 * position + 1) leftInside leftEdge least
        refine ⟨changed, ?_, contents, ordered, outside⟩
        rw [Heapq.siftChildren]
        simpa [leftInside, rightInside, readLeft, readRight, compared, less,
          Nat.add_assoc] using finished
      · have least : ∀ other (ho : other < values.length),
            Child position other → values[2 * position + 2] ≤ values[other] := by
          intro other ho linked
          rcases linked with rfl | rfl
          · exact le_of_not_gt less
          · exact le_rfl
        obtain ⟨changed, finished, contents, ordered, outside⟩ :=
          descend (2 * position + 2) rightInside rightEdge least
        refine ⟨changed, ?_, contents, ordered, outside⟩
        rw [Heapq.siftChildren]
        simpa [leftInside, rightInside, readLeft, readRight, compared, less,
          Nat.add_assoc] using finished
    · have least : ∀ other (ho : other < values.length),
          Child position other → values[2 * position + 1] ≤ values[other] := by
        intro other ho linked
        have same : other = 2 * position + 1 := by unfold Child at linked; omega
        subst other
        exact le_rfl
      obtain ⟨changed, finished, contents, ordered, outside⟩ :=
        descend (2 * position + 1) leftInside leftEdge least
      refine ⟨changed, ?_, contents, ordered, outside⟩
      rw [Heapq.siftChildren]
      simpa [leftInside, rightInside, Nat.add_assoc] using finished
  · obtain ⟨changed, finished, contents, ordered, outside⟩ :=
      siftDown_orderedBelow encode comparison
      heap address root position values positionInside below
      (sinking.leaf root values position (by omega)) found
    exact ⟨changed, by rw [Heapq.siftChildren]; simpa [leftInside] using finished,
      contents, ordered, outside⟩
termination_by size - position
decreasing_by omega

/-- The concrete heapify step repairs its subtree without moving entries outside it. -/
theorem siftUp_orderedBelow (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address root : Nat) (values : List α)
    (inside : root < values.length)
    (childrenOrdered : ∀ child, Child root child → OrderedBelow child values)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.siftUp address root heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ OrderedBelow root changed ∧ UnchangedOutside root values changed := by
  obtain ⟨changed, finished, contents, ordered, outside⟩ :=
    siftChildren_orderedBelow encode comparison
    heap address values.length root root values rfl inside .refl
    (SinkingBelow.children root values childrenOrdered) found
  exact ⟨changed, by simpa [Heapq.siftUp, Heapq.items_list heap address _ found, inside]
    using finished, contents, ordered, outside⟩

end ProjectEulerStatements.MinHeap
