import ProjectEulerStatements.Lib.MinHeapSink

/-! Local heap invariants for heapifying a subtree without assuming that its
ancestors or neighboring subtrees are ordered. -/
namespace ProjectEulerStatements.MinHeap
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

inductive Descendant (root : Nat) : Nat → Prop
  | refl : Descendant root root
  | child {parent node : Nat} : Descendant root parent → Child parent node → Descendant root node

theorem Descendant.le {root node : Nat} (below : Descendant root node) : root ≤ node := by
  induction below with
  | refl => exact Nat.le_refl _
  | child _ edge ih => exact Nat.le_trans ih (Nat.le_of_lt edge.increasing)

theorem Descendant.parent {root parent node : Nat} (below : Descendant root node)
    (different : node ≠ root) (edge : Child parent node) : Descendant root parent := by
  cases below with
  | refl => contradiction
  | child earlier linked =>
      have same := Child.unique_parent edge linked
      subst parent
      exact earlier

theorem Descendant.branch {root node : Nat} (below : Descendant root node)
    (different : node ≠ root) : ∃ first, Child root first ∧ Descendant first node := by
  induction below with
  | refl => contradiction
  | @child parent node earlier edge ih =>
      by_cases same : parent = root
      · subst parent
        exact ⟨node, edge, .refl⟩
      · obtain ⟨first, linked, rest⟩ := ih same
        exact ⟨first, linked, rest.child edge⟩

theorem Descendant.trans {first second third : Nat}
    (initial : Descendant first second) (final : Descendant second third) :
    Descendant first third := by
  induction final with
  | refl => exact initial
  | child _ edge ih => exact ih.child edge

theorem Descendant.comparable {first second node : Nat}
    (left : Descendant first node) (right : Descendant second node) :
    Descendant first second ∨ Descendant second first := by
  induction left with
  | refl => exact Or.inr right
  | @child parent node earlier edge ih =>
      by_cases same : node = second
      · subst second
        exact Or.inl (earlier.child edge)
      · exact ih (right.parent same edge)

theorem Descendant.zero (node : Nat) : Descendant 0 node := by
  induction node using Nat.strong_induction_on with
  | h node ih =>
      by_cases zero : node = 0
      · subst node
        exact .refl
      · have smaller : (node - 1) / 2 < node := by
          have := Nat.div_le_self (node - 1) 2
          omega
        exact (ih _ smaller).child (by unfold Child; omega)

def OrderedBelow (root : Nat) (items : List α) : Prop :=
  ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Descendant root parent → Child parent child → items[parent] ≤ items[child]

theorem OrderedBelow.ordered (items : List α) (ordered : OrderedBelow 0 items) : Ordered items :=
  fun parent hp child hc edge => ordered parent hp child hc (Descendant.zero parent) edge

theorem OrderedBelow.descendant (items : List α) (root node : Nat)
    (ordered : OrderedBelow root items) (below : Descendant root node) : OrderedBelow node items :=
  fun parent hp child hc rest edge => ordered parent hp child hc (below.trans rest) edge

theorem OrderedBelow.leaf (items : List α) (root : Nat) (leaf : items.length ≤ 2 * root + 1) :
    OrderedBelow root items := by
  intro parent hp child hc below edge
  have lower := below.le
  unfold Child at edge
  omega

structure RisingBelow (root : Nat) (items : List α) (position : Nat) : Prop where
  ordered : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Descendant root parent → Child parent child → child ≠ position → items[parent] ≤ items[child]
  across : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Descendant root parent → Child parent position → Child position child →
      items[parent] ≤ items[child]

structure SinkingBelow (root : Nat) (items : List α) (position : Nat) : Prop where
  ordered : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Descendant root parent → Child parent child → parent ≠ position → child ≠ position →
      items[parent] ≤ items[child]
  across : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Descendant root parent → Child parent position → Child position child →
      items[parent] ≤ items[child]

theorem RisingBelow.root (root : Nat) (items : List α) (rising : RisingBelow root items root) :
    OrderedBelow root items := by
  intro parent hp child hc below edge
  have lower := below.le
  have increasing := edge.increasing
  exact rising.ordered parent hp child hc below edge (by omega)

theorem RisingBelow.settled (root : Nat) (items : List α) (position parent : Nat)
    (inside : position < items.length) (parentInside : parent < items.length)
    (edge : Child parent position) (rising : RisingBelow root items position)
    (settled : items[parent] ≤ items[position]) : OrderedBelow root items := by
  intro above ha child hc below linked
  by_cases same : child = position
  · subst child
    have equal := Child.unique_parent linked edge
    subst above
    exact settled
  · exact rising.ordered above ha child hc below linked same

theorem RisingBelow.swap (root : Nat) (items : List α) (position parent : Nat)
    (inside : position < items.length) (parentInside : parent < items.length)
    (parentBelow : Descendant root parent) (edge : Child parent position)
    (rising : RisingBelow root items position) (smaller : items[position] < items[parent]) :
    RisingBelow root ((items.set position items[parent]).set parent items[position]) parent := by
  have parentBefore := edge.increasing
  have different : parent ≠ position := by omega
  constructor
  · intro above ha child hc below linked notParent
    simp only [List.length_set] at ha hc
    have before := linked.increasing
    by_cases aboveParent : above = parent
    · subst above
      by_cases childPosition : child = position
      · subst child
        simpa [different] using smaller.le
      · have old := rising.ordered parent parentInside child hc below linked childPosition
        have result := smaller.le.trans old
        simpa [different, notParent, childPosition, Ne.symm notParent,
          Ne.symm childPosition] using result
    · by_cases abovePosition : above = position
      · subst above
        have childPosition : child ≠ position := by omega
        have result := rising.across parent parentInside child hc parentBelow edge linked
        simpa [different, notParent, childPosition, Ne.symm notParent,
          Ne.symm childPosition] using result
      · have childPosition : child ≠ position := by
          intro same
          subst child
          exact aboveParent (Child.unique_parent linked edge)
        have result := rising.ordered above ha child hc below linked childPosition
        simpa [aboveParent, abovePosition, notParent, childPosition,
          Ne.symm aboveParent, Ne.symm abovePosition, Ne.symm notParent,
          Ne.symm childPosition] using result
  · intro above ha child hc below linked outgoing
    simp only [List.length_set] at ha hc
    have before := linked.increasing
    have afterParent := outgoing.increasing
    have aboveParent : above ≠ parent := by omega
    have abovePosition : above ≠ position := by omega
    have childParent : child ≠ parent := by omega
    have old := rising.ordered above ha parent parentInside below linked different
    by_cases childPosition : child = position
    · subst child
      simpa [different, aboveParent, abovePosition, Ne.symm aboveParent,
        Ne.symm abovePosition] using old
    · have result := old.trans
        (rising.ordered parent parentInside child hc parentBelow outgoing childPosition)
      simpa [aboveParent, abovePosition, childParent, childPosition,
        Ne.symm aboveParent, Ne.symm abovePosition, Ne.symm childParent,
        Ne.symm childPosition] using result

theorem SinkingBelow.children (root : Nat) (items : List α)
    (ordered : ∀ child, Child root child → OrderedBelow child items) :
    SinkingBelow root items root := by
  constructor
  · intro parent hp child hc below edge notParent _
    obtain ⟨first, linked, rest⟩ := below.branch notParent
    exact ordered first linked parent hp child hc rest edge
  · intro parent hp child hc below incoming _
    have lower := below.le
    have increasing := incoming.increasing
    omega

theorem SinkingBelow.leaf (root : Nat) (items : List α) (position : Nat)
    (sinking : SinkingBelow root items position) (leaf : items.length ≤ 2 * position + 1) :
    RisingBelow root items position := by
  constructor
  · intro parent hp child hc below edge notChild
    have notParent : parent ≠ position := by
      intro same
      subst parent
      unfold Child at edge
      omega
    exact sinking.ordered parent hp child hc below edge notParent notChild
  · exact sinking.across

theorem SinkingBelow.swap (root : Nat) (items : List α) (position child : Nat)
    (inside : position < items.length) (childInside : child < items.length)
    (positionBelow : Descendant root position) (edge : Child position child)
    (sinking : SinkingBelow root items position)
    (least : ∀ other (ho : other < items.length),
      Child position other → items[child] ≤ items[other]) :
    SinkingBelow root ((items.set position items[child]).set child items[position]) child := by
  have before := edge.increasing
  have different : position ≠ child := by omega
  constructor
  · intro above ha below hb within linked notAbove notBelow
    simp only [List.length_set] at ha hb
    have increasing := linked.increasing
    by_cases abovePosition : above = position
    · subst above
      have belowPosition : below ≠ position := by omega
      have result := least below hb linked
      simpa [different, Ne.symm different, notBelow, belowPosition, Ne.symm notBelow,
        Ne.symm belowPosition] using result
    · by_cases belowPosition : below = position
      · subst below
        have result := sinking.across above ha child childInside within linked edge
        simpa [different, Ne.symm different, notAbove, abovePosition, Ne.symm notAbove,
          Ne.symm abovePosition] using result
      · have result := sinking.ordered above ha below hb within linked abovePosition belowPosition
        simpa [abovePosition, belowPosition, notAbove, notBelow, Ne.symm abovePosition,
          Ne.symm belowPosition, Ne.symm notAbove, Ne.symm notBelow] using result
  · intro above ha below hb within linked outgoing
    simp only [List.length_set] at ha hb
    have same := Child.unique_parent linked edge
    subst above
    have increasing := outgoing.increasing
    have belowPosition : below ≠ position := by omega
    have belowChild : below ≠ child := by omega
    have result := sinking.ordered child childInside below hb (positionBelow.child edge)
      outgoing (Ne.symm different) belowPosition
    simpa [different, Ne.symm different, belowPosition, belowChild,
      Ne.symm belowPosition, Ne.symm belowChild] using result

section
omit [LinearOrder α]

/-- Every index outside the active subtree retains its original optional value. -/
def UnchangedOutside (root : Nat) (original changed : List α) : Prop :=
  ∀ index, ¬Descendant root index → changed[index]? = original[index]?

theorem UnchangedOutside.refl (root : Nat) (items : List α) : UnchangedOutside root items items :=
  fun _ _ => rfl

theorem UnchangedOutside.trans {root : Nat} {first second third : List α}
    (initial : UnchangedOutside root first second) (final : UnchangedOutside root second third) :
    UnchangedOutside root first third := by
  intro index outside
  exact (final index outside).trans (initial index outside)

theorem UnchangedOutside.swap (root : Nat) (items : List α) (left right : Nat)
    (leftInside : left < items.length) (rightInside : right < items.length)
    (leftBelow : Descendant root left) (rightBelow : Descendant root right) :
    UnchangedOutside root items ((items.set left items[right]).set right items[left]) := by
  intro index outside
  have notLeft : index ≠ left := by intro same; subst index; exact outside leftBelow
  have notRight : index ≠ right := by intro same; subst index; exact outside rightBelow
  simp [Ne.symm notLeft, Ne.symm notRight]

end

theorem UnchangedOutside.ordered (root other : Nat) (original changed : List α)
    (sameLength : changed.length = original.length)
    (outside : UnchangedOutside root original changed)
    (notBelow : ¬Descendant root other) (notAbove : ¬Descendant other root)
    (ordered : OrderedBelow other original) : OrderedBelow other changed := by
  intro parent hp child hc below edge
  have parentOutside : ¬Descendant root parent := by
    intro within
    exact (within.comparable below).elim notBelow notAbove
  have childOutside : ¬Descendant root child := by
    intro within
    exact (within.comparable (below.child edge)).elim notBelow notAbove
  have parentInside : parent < original.length := by omega
  have childInside : child < original.length := by omega
  have parentSame := outside parent parentOutside
  have childSame := outside child childOutside
  simp only [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem parentInside,
    Option.some.injEq] at parentSame
  simp only [List.getElem?_eq_getElem hc, List.getElem?_eq_getElem childInside,
    Option.some.injEq] at childSame
  rw [parentSame, childSame]
  exact ordered parent parentInside child childInside below edge

end ProjectEulerStatements.MinHeap
