import ProjectEulerStatements.P81

/-! Exact row recurrences and the unchanged suffix of an in-place path-sum buffer. -/
namespace ProjectEulerStatements.P81
set_option Elab.async false

@[simp] theorem firstRowFrom_length (left : Int) (row : List Int) :
    (firstRowFrom left row).length = row.length := by
  induction row generalizing left with
  | nil => rfl
  | cons x xs ih => simp [firstRowFrom, ih]

@[simp] theorem scanRow_length (left : Int) (previous row : List Int) :
    (scanRow left previous row).length = min previous.length row.length := by
  induction previous generalizing left row with
  | nil => simp [scanRow]
  | cons p ps ih => cases row <;> simp [scanRow, ih]

@[simp] theorem rowStep_length (previous row : List Int) :
    (rowStep previous row).length = min previous.length row.length := by
  cases previous <;> cases row <;> simp [rowStep]

theorem firstRowFrom_head (left : Int) (x : Int) (xs : List Int) :
    (firstRowFrom left (x :: xs))[0]? = some (left + x) := rfl

theorem firstRowFrom_recurrence (left : Int) (row : List Int) (index : Nat)
    (inside : index + 1 < row.length) :
    (firstRowFrom left row).getD (index + 1) 0 =
      (firstRowFrom left row).getD index 0 + row.getD (index + 1) 0 := by
  induction row generalizing left index with
  | nil => simp at inside
  | cons x xs ih =>
      cases index with
      | zero => cases xs <;> simp_all [firstRowFrom, List.getD]
      | succ index =>
          simpa [firstRowFrom, List.getD] using ih (left + x) index (by simpa using inside)

theorem scanRow_recurrence (left : Int) (previous row : List Int) (index : Nat)
    (inside : index < previous.length) (same : previous.length = row.length) :
    (scanRow left previous row).getD index 0 =
      row.getD index 0 + min (previous.getD index 0) ((left :: scanRow left previous row).getD index 0) := by
  induction previous generalizing left row index with
  | nil => simp at inside
  | cons p ps ih =>
      cases row with
      | nil => simp at same
      | cons x xs =>
          cases index with
          | zero => rfl
          | succ index =>
              simpa [scanRow, List.getD] using ih (x + min p left) xs index (by simpa using inside) (by simpa using same)

theorem rowStep_recurrence (previous row : List Int) (index : Nat)
    (inside : index + 1 < previous.length) (same : previous.length = row.length) :
    (rowStep previous row).getD (index + 1) 0 =
      row.getD (index + 1) 0 + min (previous.getD (index + 1) 0) ((rowStep previous row).getD index 0) := by
  cases previous with
  | nil => simp at inside
  | cons p ps =>
      cases row with
      | nil => simp at same
      | cons x xs =>
          simpa [rowStep, List.getD] using scanRow_recurrence (x + p) ps xs index (by simpa using inside) (by simpa using same)

def partialBuffer (target original : List Int) (cursor : Nat) : List Int :=
  target.take cursor ++ original.drop cursor

@[simp] theorem partialBuffer_zero (target original : List Int) : partialBuffer target original 0 = original := by
  simp [partialBuffer]

@[simp] theorem partialBuffer_length (target original : List Int) (cursor : Nat)
    (same : target.length = original.length) :
    (partialBuffer target original cursor).length = original.length := by
  simp only [partialBuffer, List.length_append, List.length_take, List.length_drop, same]
  omega

theorem partialBuffer_prefix (target original : List Int) (cursor index : Nat)
    (inside : index < cursor) (bounded : cursor ≤ target.length) :
    (partialBuffer target original cursor)[index]? = target[index]? := by
  unfold partialBuffer
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt inside]

theorem partialBuffer_suffix (target original : List Int) (cursor index : Nat)
    (after : cursor ≤ index) (bounded : cursor ≤ target.length) :
    (partialBuffer target original cursor)[index]? = original[index]? := by
  have count : (target.take cursor).length = cursor := by simp [bounded]
  unfold partialBuffer
  rw [List.getElem?_append_right (by omega), count, List.getElem?_drop]
  congr 1
  omega

theorem partialBuffer_step (target original : List Int) (cursor : Nat)
    (same : target.length = original.length) (inside : cursor < target.length) :
    (partialBuffer target original cursor).set cursor target[cursor] =
      partialBuffer target original (cursor + 1) := by
  have count : (target.take cursor).length = cursor := by simp [Nat.le_of_lt inside]
  unfold partialBuffer
  rw [List.set_append_right _ _ (by omega), count, Nat.sub_self,
    List.drop_eq_getElem_cons (by omega : cursor < original.length), List.set_cons_zero,
    List.take_succ_eq_append_getElem inside]
  simp only [List.append_assoc, List.singleton_append]

@[simp] theorem partialBuffer_finish (target original : List Int) (same : target.length = original.length) :
    partialBuffer target original original.length = target := by
  simp [partialBuffer, ← same]

theorem partialBuffer_getD_prefix (target original : List Int) (cursor index : Nat)
    (inside : index < cursor) (bounded : cursor ≤ target.length) :
    (partialBuffer target original cursor).getD index 0 = target.getD index 0 := by
  exact congrArg (fun value => value.getD 0) (partialBuffer_prefix target original cursor index inside bounded)

theorem partialBuffer_getD_suffix (target original : List Int) (cursor index : Nat)
    (after : cursor ≤ index) (bounded : cursor ≤ target.length) :
    (partialBuffer target original cursor).getD index 0 = original.getD index 0 := by
  exact congrArg (fun value => value.getD 0) (partialBuffer_suffix target original cursor index after bounded)

theorem fold_buffer (target original : List Int) (step : List Int → Nat → List Int)
    (first count : Nat) (endpoint : first + count = original.length) (same : target.length = original.length)
    (advance : ∀ index, first ≤ index → index < original.length →
      step (partialBuffer target original index) index = partialBuffer target original (index + 1)) :
    (List.range' first count).foldl step (partialBuffer target original first) = target := by
  induction count generalizing first with
  | zero =>
      have done : first = original.length := by omega
      simp [done, partialBuffer_finish target original same]
  | succ count ih =>
      rw [List.range'_succ, List.foldl_cons, advance first (by omega) (by omega)]
      exact ih (first + 1) (by omega) (fun index after valid => advance index (by omega) valid)

end ProjectEulerStatements.P81
