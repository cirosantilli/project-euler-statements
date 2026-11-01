import ProjectEulerStatements.Lib.MinHeapRise

/-! Moving the smaller child upwards can temporarily disorder both edges incident
to the displaced value. Edges across that position remain ordered, allowing the
final upward sift to restore the complete heap. -/
namespace ProjectEulerStatements.MinHeap
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

structure Sinking (items : List α) (position : Nat) : Prop where
  ordered : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Child parent child → parent ≠ position → child ≠ position → items[parent] ≤ items[child]
  across : ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    Child parent position → Child position child → items[parent] ≤ items[child]

theorem Ordered.prefix (items tail : List α) (ordered : Ordered (items ++ tail)) :
    Ordered items := by
  intro parent hp child hc edge
  have parentInside : parent < (items ++ tail).length := by simp; omega
  have childInside : child < (items ++ tail).length := by simp; omega
  simpa [List.getElem_append_left hp, List.getElem_append_left hc] using
    ordered parent parentInside child childInside edge

theorem Sinking.replace_root (root value : α) (rest : List α) (ordered : Ordered (root :: rest)) :
    Sinking (value :: rest) 0 := by
  constructor
  · intro parent hp child hc edge notParent notChild
    cases parent with
    | zero => contradiction
    | succ parent =>
        cases child with
        | zero => contradiction
        | succ child => exact ordered (parent + 1) hp (child + 1) hc edge
  · intro parent hp child hc incoming _
    have := incoming.increasing
    omega

theorem Sinking.leaf (items : List α) (position : Nat) (sinking : Sinking items position)
    (leaf : items.length ≤ 2 * position + 1) : Rising items position := by
  constructor
  · intro parent hp child hc edge notChild
    have notParent : parent ≠ position := by
      intro same
      subst parent
      unfold Child at edge
      omega
    exact sinking.ordered parent hp child hc edge notParent notChild
  · exact sinking.across

/-- Move a least child upwards while retaining the displaced value at its new position. -/
theorem Sinking.swap (items : List α) (position child : Nat)
    (inside : position < items.length) (childInside : child < items.length)
    (edge : Child position child) (sinking : Sinking items position)
    (least : ∀ other (ho : other < items.length),
      Child position other → items[child] ≤ items[other]) :
    Sinking ((items.set position items[child]).set child items[position]) child := by
  have before := edge.increasing
  have different : position ≠ child := by omega
  constructor
  · intro above ha below hb linked notAbove notBelow
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
        have result := sinking.across above ha child childInside linked edge
        simpa [different, Ne.symm different, notAbove, abovePosition, Ne.symm notAbove,
          Ne.symm abovePosition] using result
      · have result := sinking.ordered above ha below hb linked abovePosition belowPosition
        simpa [abovePosition, belowPosition, notAbove, notBelow, Ne.symm abovePosition,
          Ne.symm belowPosition, Ne.symm notAbove, Ne.symm notBelow] using result
  · intro above ha below hb linked outgoing
    simp only [List.length_set] at ha hb
    have same := Child.unique_parent linked edge
    subst above
    have increasing := outgoing.increasing
    have belowPosition : below ≠ position := by omega
    have belowChild : below ≠ child := by omega
    have result := sinking.ordered child childInside below hb outgoing (Ne.symm different)
      belowPosition
    simpa [different, Ne.symm different, belowPosition, belowChild,
      Ne.symm belowPosition, Ne.symm belowChild]
      using result

end ProjectEulerStatements.MinHeap
