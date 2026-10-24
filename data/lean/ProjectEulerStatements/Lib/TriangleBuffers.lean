import ProjectEulerStatements.Lib.TrianglePaths

/-! Prefix updates of a triangle's private row buffer preserve unread children. -/
namespace ProjectEulerStatements.P18
set_option Elab.async false
variable {α : Type*} [Add α] [Max α]

def partialRow (row below : List α) (cursor : Nat) : List α :=
  (rowTotals row below).take cursor ++ below.drop cursor

theorem rowTotals_length_of_complete (row below : List α) (complete : row.length < below.length) :
    (rowTotals row below).length = row.length := by
  rw [rowTotals_length, Nat.min_eq_left (by omega)]

theorem partialRow_zero (row below : List α) : partialRow row below 0 = below := by
  simp [partialRow]

theorem partialRow_length (row below : List α) (cursor : Nat)
    (complete : row.length < below.length) (bounded : cursor ≤ row.length) :
    (partialRow row below cursor).length = below.length := by
  simp only [partialRow, List.length_append, List.length_take,
    rowTotals_length_of_complete row below complete, Nat.min_eq_left bounded,
    List.length_drop]
  omega

theorem partialRow_suffix (row below : List α) (cursor index : Nat)
    (complete : row.length < below.length) (bounded : cursor ≤ row.length)
    (after : cursor ≤ index) :
    (partialRow row below cursor)[index]? = below[index]? := by
  have count : ((rowTotals row below).take cursor).length = cursor := by
    simp [rowTotals_length_of_complete row below complete, bounded]
  unfold partialRow
  rw [List.getElem?_append_right (by omega), count, List.getElem?_drop]
  congr 1
  omega

theorem partialRow_step (row below : List α) (cursor : Nat)
    (complete : row.length < below.length) (inside : cursor < row.length) :
    (partialRow row below cursor).set cursor
      ((rowTotals row below)[cursor]'(by
        rw [rowTotals_length_of_complete row below complete]
        omega)) =
      partialRow row below (cursor + 1) := by
  have inTotals : cursor < (rowTotals row below).length := by
    rw [rowTotals_length_of_complete row below complete]
    exact inside
  have count : ((rowTotals row below).take cursor).length = cursor := by
    simp [rowTotals_length_of_complete row below complete, Nat.min_eq_left inside.le]
  unfold partialRow
  rw [List.set_append_right _ _ (by omega), count, Nat.sub_self,
    List.drop_eq_getElem_cons (by omega : cursor < below.length), List.set_cons_zero,
    List.take_succ_eq_append_getElem inTotals]
  simp only [List.append_assoc, List.singleton_append]

theorem partialRow_finish (row below : List α) (complete : row.length < below.length) :
    (partialRow row below row.length).take row.length = rowTotals row below := by
  simp [partialRow, ← rowTotals_length_of_complete row below complete]

theorem rowTotals_take (row below : List α) (width : Nat) (enough : row.length < width) :
    rowTotals row (below.take width) = rowTotals row below := by
  apply List.ext_getElem?
  intro index
  rw [rowTotals_getElem?, rowTotals_getElem?]
  by_cases inside : index < row.length
  · rw [List.getElem?_take_of_lt (by omega : index < width),
      List.getElem?_take_of_lt (by omega : index + 1 < width)]
  · simp [List.getElem?_eq_none (by omega : row.length ≤ index)]

/-- Only the active prefix is needed for the next row's adjacent-child recurrence. -/
theorem reducePrefix_buffer_step (rows : List (List α)) (count : Nat) (buffer : List α)
    (inside : count < rows.length) (shape : rows[count].length = count + 1)
    (room : count + 1 < buffer.length) :
    reducePrefix rows (count + 1) (buffer.take (count + 2)) =
      reducePrefix rows count ((partialRow rows[count] buffer (count + 1)).take (count + 1)) := by
  rw [reducePrefix_succ rows count _ inside, rowTotals_take _ _ _ (by omega)]
  rw [← shape, partialRow_finish _ _ (by omega)]

end ProjectEulerStatements.P18
