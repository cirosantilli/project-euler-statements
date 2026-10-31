import ProjectEulerStatements.Lib.HeapqSubtree

/-! Compose concrete subtree repairs along a children-before-parents traversal.
The pending nodes contain every pending node's ancestors; completed subtrees
retain their order as the traversal removes one pending node at a time. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

def BottomUp (positions : List Nat) : Prop :=
  positions.Pairwise (fun earlier later => ¬Descendant earlier later)

def AncestorClosed (positions : List Nat) : Prop :=
  ∀ node ∈ positions, ∀ ancestor, Descendant ancestor node → ancestor ∈ positions

theorem siftAll_ordered (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address : Nat) (values : List α) (positions : List Nat)
    (found : heap[address]? = some (.list (values.map encode)))
    (valid : ∀ position ∈ positions, position < values.length)
    (traversal : BottomUp positions) (closed : AncestorClosed positions)
    (completed : ∀ root, root ∉ positions → OrderedBelow root values) :
    ∃ changed, Heapq.siftAll address positions heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed := by
  induction positions generalizing heap values with
  | nil =>
      have unchanged : heap.set address (.list (values.map encode)) = heap := by
        obtain ⟨bounded, entry⟩ := List.getElem?_eq_some_iff.mp found
        rw [← entry, List.set_getElem_self bounded]
      exact ⟨values, by simp [Heapq.siftAll, unchanged], .refl _,
        (completed 0 (by simp)).ordered values⟩
  | cons position rest ih =>
      obtain ⟨later, remaining⟩ := List.pairwise_cons.mp traversal
      have childrenOrdered : ∀ child, Child position child → OrderedBelow child values := by
        intro child edge
        apply completed child
        intro member
        rcases List.mem_cons.mp member with same | tail
        · have before := edge.increasing
          omega
        · exact later child tail (Descendant.refl.child edge)
      obtain ⟨middle, first, permutation, ordered, outside⟩ :=
        siftUp_orderedBelow encode comparison heap address position values
          (valid position (by simp)) childrenOrdered found
      have closedRest : AncestorClosed rest := by
        intro node member ancestor below
        have present := closed node (by simp [member]) ancestor below
        rcases List.mem_cons.mp present with same | tail
        · subst ancestor
          exact False.elim (later node member below)
        · exact tail
      have completedRest : ∀ root, root ∉ rest → OrderedBelow root middle := by
        intro root absent
        by_cases same : root = position
        · subst root
          exact ordered
        · by_cases below : Descendant position root
          · exact ordered.descendant middle position root below
          · have notPending : root ∉ position :: rest := by simp [same, absent]
            have notAbove : ¬Descendant root position := by
              intro above
              exact notPending (closed position (by simp) root above)
            exact outside.ordered position root values middle permutation.length_eq below notAbove
              (completed root notPending)
      have addressValid := (List.getElem?_eq_some_iff.mp found).1
      obtain ⟨changed, finished, contents, resultOrdered⟩ := ih
        (heap.set address (.list (middle.map encode))) middle (by simp [addressValid])
        (fun index member => by
          rw [permutation.length_eq]
          exact valid index (by simp [member])) remaining closedRest completedRest
      exact ⟨changed, by simp [Heapq.siftAll, first, finished], contents.trans permutation,
        resultOrdered⟩

/-- Visiting every internal node in bottom-up order suffices for arbitrary input values. -/
theorem siftAll_ordered_of_complete (encode : α → Mutable.Value)
    (comparison : EncodesOrder encode) (heap : Mutable.Heap) (address : Nat)
    (values : List α) (positions : List Nat)
    (found : heap[address]? = some (.list (values.map encode)))
    (traversal : BottomUp positions)
    (complete : ∀ index, index ∈ positions ↔ index < values.length / 2) :
    ∃ changed, Heapq.siftAll address positions heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed := by
  apply siftAll_ordered encode comparison heap address values positions found
  · intro position member
    have bound := (complete position).mp member
    omega
  · exact traversal
  · intro node member ancestor below
    apply (complete ancestor).mpr
    have bound := (complete node).mp member
    have lower := below.le
    omega
  · intro root absent
    apply OrderedBelow.leaf values root
    have outside : ¬root < values.length / 2 := by simpa only [← complete root] using absent
    omega

theorem BottomUp.reverse_range (size : Nat) : BottomUp (List.range size).reverse := by
  apply List.pairwise_reverse.mpr
  have increasing : (List.range size).Pairwise (· < ·) := by
    simpa only [List.range_eq_range'] using (List.pairwise_lt_range' (s := 0) (n := size))
  apply increasing.imp
  intro earlier later smaller below
  have lower := below.le
  omega

end ProjectEulerStatements.MinHeap
