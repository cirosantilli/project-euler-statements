import ProjectEulerStatements.Lib.MinHeap

/-! The invariant for moving an inserted heap element towards the root.
Besides the potentially disordered incoming edge, the parent's value must precede
the active node's children: the parent will occupy that node after a swap. -/
namespace ProjectEulerStatements.MinHeap
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

def Child (parent child : Nat) : Prop := child = 2 * parent + 1 ∨ child = 2 * parent + 2

theorem Child.increasing {parent child : Nat} (edge : Child parent child) : parent < child := by
  unfold Child at edge
  omega

theorem Child.unique_parent {first second child : Nat}
    (a : Child first child) (b : Child second child) : first = second := by
  unfold Child at a b
  omega

structure Rising (items : List α) (position : Nat) : Prop where
  ordered : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Child parent child → child ≠ position → items[parent] ≤ items[child]
  across : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Child parent position → Child position child → items[parent] ≤ items[child]

theorem Rising.append (items : List α) (value : α) (ordered : Ordered items) :
    Rising (items ++ [value]) items.length := by
  constructor
  · intro parent hp child hc edge different
    have smaller := edge.increasing
    have childInside : child < items.length := by
      simp only [List.length_append, List.length_singleton] at hc
      omega
    have parentInside := Nat.lt_trans smaller childInside
    simpa [List.getElem_append_left parentInside, List.getElem_append_left childInside] using
      ordered parent parentInside child childInside edge
  · intro parent hp child hc _ edge
    have smaller := edge.increasing
    simp only [List.length_append, List.length_singleton] at hc
    omega

theorem Rising.root (items : List α) (rising : Rising items 0) : Ordered items := by
  intro parent hp child hc edge
  exact rising.ordered parent hp child hc edge (by have := Child.increasing edge; omega)

theorem Rising.settled (items : List α) (position parent : Nat)
    (inside : position < items.length) (parentInside : parent < items.length)
    (edge : Child parent position) (rising : Rising items position)
    (settled : items[parent] ≤ items[position]) : Ordered items := by
  intro above ha child hc linked
  by_cases same : child = position
  · subst child
    have equal := Child.unique_parent linked edge
    subst above
    exact settled
  · exact rising.ordered above ha child hc linked same

/-- Swapping the active value with its larger parent moves the invariant up one edge. -/
theorem Rising.swap (items : List α) (position parent : Nat)
    (inside : position < items.length) (parentInside : parent < items.length)
    (edge : Child parent position) (rising : Rising items position)
    (smaller : items[position] < items[parent]) :
    Rising ((items.set position items[parent]).set parent items[position]) parent := by
  have parentBefore := edge.increasing
  have different : parent ≠ position := by omega
  constructor
  · intro above ha child hc linked notParent
    simp only [List.length_set] at ha hc
    have before := linked.increasing
    by_cases aboveParent : above = parent
    · subst above
      by_cases childPosition : child = position
      · subst child
        simpa [different] using smaller.le
      · have old := rising.ordered parent parentInside child hc linked childPosition
        have result := smaller.le.trans old
        simpa [different, notParent, childPosition, Ne.symm notParent,
          Ne.symm childPosition] using result
    · by_cases abovePosition : above = position
      · subst above
        have childPosition : child ≠ position := by omega
        have result := rising.across parent parentInside child hc edge linked
        simpa [different, notParent, childPosition, Ne.symm notParent,
          Ne.symm childPosition] using result
      · have childPosition : child ≠ position := by
          intro same
          subst child
          exact aboveParent (Child.unique_parent linked edge)
        have result := rising.ordered above ha child hc linked childPosition
        simpa [aboveParent, abovePosition, notParent, childPosition,
          Ne.symm aboveParent, Ne.symm abovePosition, Ne.symm notParent,
          Ne.symm childPosition] using result
  · intro above ha child hc linked outgoing
    simp only [List.length_set] at ha hc
    have before := linked.increasing
    have afterParent := outgoing.increasing
    have aboveParent : above ≠ parent := by omega
    have abovePosition : above ≠ position := by omega
    have childParent : child ≠ parent := by omega
    have old := rising.ordered above ha parent parentInside linked different
    by_cases childPosition : child = position
    · subst child
      simpa [different, aboveParent, abovePosition, Ne.symm aboveParent,
        Ne.symm abovePosition] using old
    · have result := old.trans (rising.ordered parent parentInside child hc outgoing childPosition)
      simpa [aboveParent, abovePosition, childParent, childPosition,
        Ne.symm aboveParent, Ne.symm abovePosition, Ne.symm childParent,
        Ne.symm childPosition] using result

end ProjectEulerStatements.MinHeap
