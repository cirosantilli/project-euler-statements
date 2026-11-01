import ProjectEulerStatements.P82
import ProjectEulerStatements.Lib.GridPathRows
import Mathlib.Data.List.GetD

/-! Indexed recurrences for the two vertical path-sum relaxation passes. -/
namespace ProjectEulerStatements.P82
set_option Elab.async false

@[simp] theorem getCol_length (matrix : List (List Int)) (column : Nat) :
    (getCol matrix column).length = matrix.length := by simp [getCol]

@[simp] theorem addLists_length (left right : List Int) (same : left.length = right.length) :
    (addLists left right).length = left.length := by simp [addLists, same]

@[simp] theorem relaxTail_length (previous : Int) (cost column : List Int) :
    (relaxTail previous cost column).length = min cost.length column.length := by
  induction cost generalizing previous column with
  | nil => simp [relaxTail]
  | cons c cs ih => cases column <;> simp [relaxTail, ih]

@[simp] theorem relaxDown_length (cost column : List Int) (same : cost.length = column.length) :
    (relaxDown cost column).length = cost.length := by
  cases cost <;> cases column <;> simp_all [relaxDown]

@[simp] theorem relaxUp_length (cost column : List Int) (same : cost.length = column.length) :
    (relaxUp cost column).length = cost.length := by
  unfold relaxUp
  rw [List.length_reverse, relaxDown_length cost.reverse column.reverse (by simpa using same), List.length_reverse]

@[simp] theorem columnStep_length (previous column : List Int) (same : previous.length = column.length) :
    (columnStep previous column).length = previous.length := by
  have added := addLists_length previous column same
  have down := relaxDown_length (addLists previous column) column (by omega)
  have up := relaxUp_length (relaxDown (addLists previous column) column) column (by omega)
  simpa only [columnStep] using up.trans (down.trans added)

theorem relaxTail_recurrence (previous : Int) (cost column : List Int) (index : Nat)
    (inside : index < cost.length) (same : cost.length = column.length) :
    (relaxTail previous cost column).getD index 0 =
      min (cost.getD index 0) ((previous :: relaxTail previous cost column).getD index 0 + column.getD index 0) := by
  induction cost generalizing previous column index with
  | nil => simp at inside
  | cons c cs ih =>
      cases column with
      | nil => simp at same
      | cons v vs =>
          cases index with
          | zero => rfl
          | succ index =>
              simpa [relaxTail, List.getD] using ih (min c (previous + v)) vs index
                (by simpa using inside) (by simpa using same)

theorem relaxDown_recurrence (cost column : List Int) (index : Nat)
    (inside : index + 1 < cost.length) (same : cost.length = column.length) :
    (relaxDown cost column).getD (index + 1) 0 =
      min (cost.getD (index + 1) 0) ((relaxDown cost column).getD index 0 + column.getD (index + 1) 0) := by
  cases cost with
  | nil => simp at inside
  | cons c cs =>
      cases column with
      | nil => simp at same
      | cons v vs =>
          simpa [relaxDown, same, List.getD] using relaxTail_recurrence c cs vs index
            (by simpa using inside) (by simpa using same)

end ProjectEulerStatements.P82
