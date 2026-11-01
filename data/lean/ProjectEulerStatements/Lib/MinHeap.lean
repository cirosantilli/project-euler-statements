import ProjectEulerStatements.Lib.TopologicalOrder

/-! Binary heap order implies least-element selection for arbitrary finite lists. -/
namespace ProjectEulerStatements.MinHeap
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

/-- Each stored parent precedes both of its stored children. -/
def Ordered (items : List α) : Prop :=
  ∀ parent (hp : parent < items.length) child (hc : child < items.length),
    child = 2 * parent + 1 ∨ child = 2 * parent + 2 → items[parent] ≤ items[child]

theorem root_le_getElem (items : List α) (ordered : Ordered items)
    (nonempty : 0 < items.length) (index : Nat) (valid : index < items.length) :
    items[0] ≤ items[index] := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      by_cases zero : index = 0
      · subst index
        exact le_rfl
      · let parent := (index - 1) / 2
        have smaller : parent < index := by
          have := Nat.div_le_self (index - 1) 2
          omega
        have parentValid : parent < items.length := by omega
        have child : index = 2 * parent + 1 ∨ index = 2 * parent + 2 := by
          dsimp [parent]
          omega
        exact (ih parent smaller parentValid).trans (ordered parent parentValid index valid child)

theorem head_le_mem (head : α) (rest : List α) (ordered : Ordered (head :: rest))
    (value : α) (member : value ∈ head :: rest) : head ≤ value := by
  obtain ⟨index, valid, rfl⟩ := List.mem_iff_getElem.mp member
  exact root_le_getElem (head :: rest) ordered (by simp) index valid

theorem min?_eq_head (head : α) (rest : List α) (ordered : Ordered (head :: rest)) :
    (head :: rest).min? = some head := by
  apply List.min?_eq_some_iff.mpr
  exact ⟨by simp, head_le_mem head rest ordered⟩

/-- A heap containing exactly the eligible vertices chooses the greedy model's vertex. -/
theorem head_eq_choose (nodes : List α) (edges : List (α × α)) (head : α) (rest : List α)
    (contents : (head :: rest).Perm
      (nodes.filter (fun vertex => decide (TopologicalOrder.Ready vertex edges))))
    (ordered : Ordered (head :: rest)) :
    TopologicalOrder.choose nodes edges = some head := by
  apply List.min?_eq_some_iff.mpr
  exact ⟨contents.mem_iff.mp (by simp),
    fun value member => head_le_mem head rest ordered value (contents.mem_iff.mpr member)⟩

end ProjectEulerStatements.MinHeap
