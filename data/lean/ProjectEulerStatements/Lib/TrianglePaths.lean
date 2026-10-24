import ProjectEulerStatements.P18

/-! Bottom-up row reduction for maximum paths through a triangle. -/
namespace ProjectEulerStatements.P18

/-- The adjacent-child recurrence also applies to signed weights and ragged rows. -/
def rowTotals {α : Type*} [Add α] [Max α] (row below : List α) : List α :=
  (row.zip (below.zip below.tail)).map (fun (x, y, z) => x + max y z)

/-- Bottom-up reduction of possibly ragged rows with arbitrary ordered weights. -/
def reduceRowValues {α : Type*} [Add α] [Max α] (rows : List (List α)) : List α :=
  match rows.reverse with
  | [] => []
  | bottom :: rest => rest.foldl (fun acc row => rowTotals row acc) bottom

/-- Reduce the first `count` rows above an already-computed row of totals. -/
def reducePrefix {α : Type*} [Add α] [Max α]
    (rows : List (List α)) (count : Nat) (below : List α) : List α :=
  (rows.take count).reverse.foldl (fun acc row => rowTotals row acc) below

theorem reducePrefix_succ {α : Type*} [Add α] [Max α]
    (rows : List (List α)) (count : Nat) (below : List α) (valid : count < rows.length) :
    reducePrefix rows (count + 1) below =
      reducePrefix rows count (rowTotals rows[count] below) := by
  unfold reducePrefix
  rw [List.take_succ_eq_append_getElem valid, List.reverse_append]
  rfl

theorem reduceRowValues_from_last {α : Type*} [Add α] [Max α]
    (rows : List (List α)) (nonempty : rows ≠ []) :
    reduceRowValues rows = reducePrefix rows (rows.length - 1)
      (rows[rows.length - 1]'(by have := List.length_pos_iff.mpr nonempty; omega)) := by
  have last : rows.length - 1 < rows.length := by
    have := List.length_pos_iff.mpr nonempty
    omega
  have splitRows : rows = rows.take (rows.length - 1) ++ [rows[rows.length - 1]] := by
    rw [← List.take_succ_eq_append_getElem last,
      Nat.sub_add_cancel (by omega : 1 ≤ rows.length), List.take_length]
  unfold reduceRowValues
  conv_lhs => rw [splitRows, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append]
  rfl

theorem rowTotals_length {α : Type*} [Add α] [Max α] (row below : List α) :
    (rowTotals row below).length = min row.length (below.length - 1) := by
  simp [rowTotals]

theorem rowTotals_getElem? {α : Type*} [Add α] [Max α]
    (row below : List α) (i : Nat) :
    (rowTotals row below)[i]? = (do
      let x ← row[i]?
      let y ← below[i]?
      let z ← below[i + 1]?
      pure (x + max y z)) := by
  simp only [rowTotals, List.getElem?_map, List.zip, List.getElem?_zipWith, List.getElem?_tail]
  cases row[i]? <;> cases below[i]? <;> cases below[i + 1]? <;> rfl

theorem maxRow_eq_rowTotals (row below : List Nat) : maxRow row below = rowTotals row below := by
  induction row generalizing below with
  | nil => simp [maxRow, rowTotals]
  | cons x xs ih =>
      cases below with
      | nil => simp [maxRow, rowTotals]
      | cons y ys =>
          cases ys with
          | nil => simp [maxRow, rowTotals]
          | cons z zs =>
              simpa [maxRow, rowTotals] using
                congrArg (fun rest => (x + max y z) :: rest) (ih (z :: zs))

/-- Pair each entry with the larger of its two children, truncating incomplete rows. -/
theorem maxRow_length (row below : List Nat) :
    (maxRow row below).length = min row.length (below.length - 1) := by
  induction row generalizing below with
  | nil => simp [maxRow]
  | cons x xs ih =>
      cases below with
      | nil => simp [maxRow]
      | cons y ys =>
          cases ys with
          | nil => simp [maxRow]
          | cons z zs => simp [maxRow, ih]

/-- The local recurrence expressed without requiring bounds on either row. -/
theorem maxRow_getElem? (row below : List Nat) (i : Nat) :
    (maxRow row below)[i]? = (do
      let x ← row[i]?
      let y ← below[i]?
      let z ← below[i + 1]?
      pure (x + max y z)) := by
  induction row generalizing below i with
  | nil => simp [maxRow]
  | cons x xs ih =>
      cases below with
      | nil => cases i <;> simp [maxRow]
      | cons y ys =>
          cases ys with
          | nil => cases i <;> simp [maxRow]
          | cons z zs => cases i <;> simp [maxRow, ih]

/-- Retain the top row of totals after combining all rows below it. -/
def reduceRows (rows : List (List Nat)) : List Nat :=
  match rows.reverse with
  | [] => []
  | bottom :: rest => rest.foldl (fun acc row => maxRow row acc) bottom

theorem reduceRows_eq_reduceRowValues (rows : List (List Nat)) :
    reduceRows rows = reduceRowValues rows := by
  have same : (fun acc row => maxRow row acc) = (fun acc row => rowTotals row acc) :=
    funext fun acc => funext fun row => maxRow_eq_rowTotals row acc
  cases backwards : rows.reverse <;> simp [reduceRows, reduceRowValues, backwards, same]

theorem reduceRows_length_le_first (row : List Nat) (rest : List (List Nat)) :
    (reduceRows (row :: rest)).length ≤ row.length := by
  cases reversed : rest.reverse with
  | nil => simp [reduceRows, List.reverse_cons, reversed]
  | cons bottom rows =>
      simp only [reduceRows, List.reverse_cons, reversed, List.cons_append,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [maxRow_length]
      exact Nat.min_le_left _ _

theorem naive_eq_reduceRows (tri : Triangle) : naive tri = (reduceRows tri.1)[0]?.getD 0 := by
  cases reversed : tri.1.reverse <;> simp [naive, reduceRows, reversed, List.getD]

theorem reduceRows_triangle_length (tri : Triangle) : (reduceRows tri.1).length ≤ 1 := by
  cases rows : tri.1 with
  | nil => simp [reduceRows]
  | cons row rest =>
      have first := tri.property 0 (by simp [rows])
      have size : row.length = 1 := by simpa [rows] using first
      simpa [size] using reduceRows_length_le_first row rest

end ProjectEulerStatements.P18
