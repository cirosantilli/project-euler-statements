import ProjectEulerStatements.Lib.Grid
import ProjectEulerStatements.Lib.ListMaximum

/-! Candidate enumeration for products of adjacent grid entries. -/
namespace ProjectEulerStatements.Grid

/-- Signed row/column increments of the four forward directions. -/
def Direction.rowStep : Direction → Int
  | .right => 0
  | _ => 1

def Direction.columnStep : Direction → Int
  | .down => 0
  | .downLeft => -1
  | _ => 1

theorem Direction.row_eq (direction : Direction) (start : Int) (position : Nat) :
    direction.row start position = start + position * direction.rowStep := by
  cases direction <;> simp [Direction.row, Direction.rowStep]

theorem Direction.column_eq (direction : Direction) (start : Int) (position : Nat) :
    direction.column start position = start + position * direction.columnStep := by
  cases direction <;> simp [Direction.column, Direction.columnStep, sub_eq_add_neg]

/-- Both endpoints lie in a rectangle. For positive counts, every intermediate
point is then in bounds by `segment_bounds`. -/
def ValidStart (direction : Direction) (rows columns count r c : Nat) : Prop :=
  r < rows ∧ c < columns ∧
    (0 ≤ (r : Int) + ((count : Int) - 1) * direction.rowStep ∧
      (r : Int) + ((count : Int) - 1) * direction.rowStep < rows) ∧
    (0 ≤ (c : Int) + ((count : Int) - 1) * direction.columnStep ∧
      (c : Int) + ((count : Int) - 1) * direction.columnStep < columns)
deriving Decidable

theorem validStart_right (rows columns count r c : Nat) (positive : 0 < count) :
    ValidStart .right rows columns count r c ↔ r < rows ∧ c + count ≤ columns := by
  simp only [ValidStart, Direction.rowStep, Direction.columnStep, mul_zero, add_zero, mul_one]
  omega

theorem validStart_down (rows columns count r c : Nat) (positive : 0 < count) :
    ValidStart .down rows columns count r c ↔ r + count ≤ rows ∧ c < columns := by
  simp only [ValidStart, Direction.rowStep, Direction.columnStep, mul_zero, add_zero, mul_one]
  omega

theorem validStart_downRight (rows columns count r c : Nat) (positive : 0 < count) :
    ValidStart .downRight rows columns count r c ↔ r + count ≤ rows ∧ c + count ≤ columns := by
  simp only [ValidStart, Direction.rowStep, Direction.columnStep, mul_one]
  omega

theorem validStart_downLeft (rows columns count r c : Nat) (positive : 0 < count) :
    ValidStart .downLeft rows columns count r c ↔
      r + count ≤ rows ∧ count - 1 ≤ c ∧ c < columns := by
  simp only [ValidStart, Direction.rowStep, Direction.columnStep, mul_one, mul_neg_one]
  omega

/-- Direction-specific starting positions, with the left diagonal shifted to
its upper-right endpoint. -/
def starts (direction : Direction) (rows columns count : Nat) : List (Nat × Nat) :=
  match direction with
  | .right => (List.range rows).flatMap fun r =>
      (List.range (columns + 1 - count)).map fun c => (r, c)
  | .down => (List.range (rows + 1 - count)).flatMap fun r =>
      (List.range columns).map fun c => (r, c)
  | .downRight => (List.range (rows + 1 - count)).flatMap fun r =>
      (List.range (columns + 1 - count)).map fun c => (r, c)
  | .downLeft => (List.range (rows + 1 - count)).flatMap fun r =>
      (List.range (columns + 1 - count)).map fun c => (r, c + (count - 1))

theorem mem_starts_iff (direction : Direction) (rows columns count r c : Nat)
    (positive : 0 < count) :
    (r, c) ∈ starts direction rows columns count ↔ ValidStart direction rows columns count r c := by
  cases direction with
  | right =>
      rw [validStart_right _ _ _ _ _ positive]
      simp only [starts, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨a, ha, b, hb, rfl, rfl⟩
        omega
      · rintro ⟨hr, hc⟩
        exact ⟨r, hr, c, by omega, rfl, rfl⟩
  | down =>
      rw [validStart_down _ _ _ _ _ positive]
      simp only [starts, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨a, ha, b, hb, rfl, rfl⟩
        omega
      · rintro ⟨hr, hc⟩
        exact ⟨r, by omega, c, hc, rfl, rfl⟩
  | downRight =>
      rw [validStart_downRight _ _ _ _ _ positive]
      simp only [starts, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨a, ha, b, hb, rfl, rfl⟩
        omega
      · rintro ⟨hr, hc⟩
        exact ⟨r, by omega, c, by omega, rfl, rfl⟩
  | downLeft =>
      rw [validStart_downLeft _ _ _ _ _ positive]
      simp only [starts, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨a, ha, b, hb, rfl, rfl⟩
        omega
      · rintro ⟨hr, hc, hc'⟩
        exact ⟨r, by omega, c - (count - 1), by omega, rfl, by omega⟩

/-- Padding outside the supplied grid is zero; valid rectangular callers never
read this padding. -/
def segmentProduct (grid : List (List Nat)) (direction : Direction)
    (r c : Nat) (count : Nat) : Nat :=
  (List.range count).foldl
    (fun acc position =>
      acc * get grid (direction.row r position) (direction.column c position) 0) 1

/-- The product of the unvisited suffix of a segment. -/
def segmentTail (grid : List (List Nat)) (direction : Direction)
    (r c position count : Nat) : Nat :=
  ((List.range' position (count - position)).map fun index =>
    get grid (direction.row r index) (direction.column c index) 0).prod

theorem segmentTail_done (grid : List (List Nat)) (direction : Direction)
    (r c position count : Nat) (finished : count ≤ position) :
    segmentTail grid direction r c position count = 1 := by
  simp [segmentTail, Nat.sub_eq_zero_of_le finished]

theorem segmentTail_step (grid : List (List Nat)) (direction : Direction)
    (r c position count : Nat) (active : position < count) :
    segmentTail grid direction r c position count =
      get grid (direction.row r position) (direction.column c position) 0 *
        segmentTail grid direction r c (position + 1) count := by
  have remaining : count - position = count - (position + 1) + 1 := by omega
  rw [segmentTail, remaining, List.range'_succ]
  simp only [List.map_cons, List.prod_cons]
  rfl

theorem segmentTail_zero (grid : List (List Nat)) (direction : Direction) (r c count : Nat) :
    segmentTail grid direction r c 0 count = segmentProduct grid direction r c count := by
  simp [segmentTail, segmentProduct, List.range_eq_range', List.prod_eq_foldl, List.foldl_map]

/-- The downward-left scan starts at the upper-right end of each candidate. -/
def columnStart (direction : Direction) (column count : Nat) : Nat :=
  match direction with
  | .downLeft => column + (count - 1)
  | _ => column

/-- Unvisited products in one row of a direction-specific enumeration. -/
def rowProducts (grid : List (List Nat)) (direction : Direction)
    (row count position stop : Nat) : List Nat :=
  (List.range' position (stop - position)).map fun column =>
    segmentProduct grid direction row (columnStart direction column count) count

theorem rowProducts_done (grid : List (List Nat)) (direction : Direction)
    (row count position stop : Nat) (finished : stop ≤ position) :
    rowProducts grid direction row count position stop = [] := by
  simp [rowProducts, Nat.sub_eq_zero_of_le finished]

theorem rowProducts_step (grid : List (List Nat)) (direction : Direction)
    (row count position stop : Nat) (active : position < stop) :
    rowProducts grid direction row count position stop =
      segmentProduct grid direction row (columnStart direction position count) count ::
        rowProducts grid direction row count (position + 1) stop := by
  have remaining : stop - position = stop - (position + 1) + 1 := by omega
  rw [rowProducts, remaining, List.range'_succ]
  rfl

/-- Unvisited rows in a direction-specific enumeration. -/
def gridProductsTail (grid : List (List Nat)) (direction : Direction)
    (count position rowStop columnStop : Nat) : List Nat :=
  (List.range' position (rowStop - position)).flatMap fun row =>
    rowProducts grid direction row count 0 columnStop

theorem gridProductsTail_done (grid : List (List Nat)) (direction : Direction)
    (count position rowStop columnStop : Nat) (finished : rowStop ≤ position) :
    gridProductsTail grid direction count position rowStop columnStop = [] := by
  simp [gridProductsTail, Nat.sub_eq_zero_of_le finished]

theorem gridProductsTail_step (grid : List (List Nat)) (direction : Direction)
    (count position rowStop columnStop : Nat) (active : position < rowStop) :
    gridProductsTail grid direction count position rowStop columnStop =
      rowProducts grid direction position count 0 columnStop ++
        gridProductsTail grid direction count (position + 1) rowStop columnStop := by
  have remaining : rowStop - position = rowStop - (position + 1) + 1 := by omega
  rw [gridProductsTail, remaining, List.range'_succ]
  rfl

theorem gridProductsTail_zero (grid : List (List Nat)) (direction : Direction)
    (rows columns count : Nat) :
    gridProductsTail grid direction count 0
        (if direction = .right then rows else rows + 1 - count)
        (if direction = .down then columns else columns + 1 - count) =
      (starts direction rows columns count).map fun (r, c) =>
        segmentProduct grid direction r c count := by
  cases direction <;>
    simp [gridProductsTail, rowProducts, columnStart, starts, List.map_flatMap,
      List.map_map, Function.comp_def, List.range_eq_range']

def directions : List Direction := [.right, .down, .downRight, .downLeft]

/-- Enumerate one direction at a time, as the reference implementation does. -/
def directionalProducts (grid : List (List Nat)) (rows columns count : Nat) : List Nat :=
  directions.flatMap fun direction => (starts direction rows columns count).map fun (r, c) =>
    segmentProduct grid direction r c count

/-- Update a running maximum with one direction, rejecting invalid endpoints. -/
def scanDirection (grid : List (List Nat)) (rows columns count r c best : Nat)
    (direction : Direction) : Nat :=
  if ValidStart direction rows columns count r c then
    max best (segmentProduct grid direction r c count) else best

/-- Testing directions and updating the maximum equals collecting the valid
products first and then taking their maximum. -/
theorem fold_scanDirection (grid : List (List Nat)) (rows columns count r c : Nat)
    (choices : List Direction) (best : Nat) :
    choices.foldl (scanDirection grid rows columns count r c) best =
      (choices.filterMap fun direction =>
        if ValidStart direction rows columns count r c then
          some (segmentProduct grid direction r c count) else none).foldl max best := by
  induction choices generalizing best with
  | nil => rfl
  | cons direction choices ih =>
      by_cases valid : ValidStart direction rows columns count r c
      · simp [scanDirection, valid, ih]
      · simp [scanDirection, valid, ih]

/-- Enumerate one cell at a time, testing direction endpoints, as the optimized
implementation does. -/
def scannedProducts (grid : List (List Nat)) (rows columns count : Nat) : List Nat :=
  (List.range rows).flatMap fun r => (List.range columns).flatMap fun c =>
    directions.filterMap fun direction =>
      if ValidStart direction rows columns count r c then
        some (segmentProduct grid direction r c count) else none

/-- Remaining candidates in one row of a cell-first scan. -/
def scanRowTail (grid : List (List Nat)) (rows columns count r position : Nat) : List Nat :=
  (List.range' position (columns - position)).flatMap fun c =>
    directions.filterMap fun direction =>
      if ValidStart direction rows columns count r c then
        some (segmentProduct grid direction r c count) else none

theorem scanRowTail_done (grid : List (List Nat)) (rows columns count r position : Nat)
    (finished : columns ≤ position) : scanRowTail grid rows columns count r position = [] := by
  simp [scanRowTail, Nat.sub_eq_zero_of_le finished]

theorem scanRowTail_step (grid : List (List Nat)) (rows columns count r position : Nat)
    (active : position < columns) :
    scanRowTail grid rows columns count r position =
      (directions.filterMap fun direction =>
        if ValidStart direction rows columns count r position then
          some (segmentProduct grid direction r position count) else none) ++
        scanRowTail grid rows columns count r (position + 1) := by
  have remaining : columns - position = columns - (position + 1) + 1 := by omega
  rw [scanRowTail, remaining, List.range'_succ]
  rfl

/-- Remaining complete rows of a cell-first scan. -/
def scanGridTail (grid : List (List Nat)) (rows columns count position : Nat) : List Nat :=
  (List.range' position (rows - position)).flatMap fun r => scanRowTail grid rows columns count r 0

theorem scanGridTail_done (grid : List (List Nat)) (rows columns count position : Nat)
    (finished : rows ≤ position) : scanGridTail grid rows columns count position = [] := by
  simp [scanGridTail, Nat.sub_eq_zero_of_le finished]

theorem scanGridTail_step (grid : List (List Nat)) (rows columns count position : Nat)
    (active : position < rows) :
    scanGridTail grid rows columns count position =
      scanRowTail grid rows columns count position 0 ++
      scanGridTail grid rows columns count (position + 1) := by
  have remaining : rows - position = rows - (position + 1) + 1 := by omega
  rw [scanGridTail, remaining, List.range'_succ]
  rfl

theorem scanGridTail_zero (grid : List (List Nat)) (rows columns count : Nat) :
    scanGridTail grid rows columns count 0 = scannedProducts grid rows columns count := by
  simp [scanGridTail, scanRowTail, scannedProducts, List.range_eq_range']

theorem mem_scannedProducts_iff (grid : List (List Nat)) (rows columns count value : Nat) :
    value ∈ scannedProducts grid rows columns count ↔
      ∃ direction ∈ directions, ∃ r c, ValidStart direction rows columns count r c ∧
        segmentProduct grid direction r c count = value := by
  simp only [scannedProducts, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, c, hc, direction, member, result⟩
    split at result
    · exact ⟨direction, member, r, c, by assumption, Option.some.inj result⟩
    · contradiction
  · rintro ⟨direction, member, r, c, valid, rfl⟩
    exact ⟨r, valid.1, c, valid.2.1, direction, member, by simp [valid]⟩

/-- The searches differ only in ordering when the requested segment is nonempty. -/
theorem maximum_directional_eq_scanned (grid : List (List Nat)) (rows columns count : Nat)
    (positive : 0 < count) :
    (directionalProducts grid rows columns count).foldl max 0 =
      (scannedProducts grid rows columns count).foldl max 0 := by
  apply ListMaximum.eq_of_same_members
  intro value
  rw [mem_scannedProducts_iff]
  simp only [directionalProducts, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨direction, member, ⟨r, c⟩, present, rfl⟩
    exact ⟨direction, member, r, c, (mem_starts_iff _ _ _ _ _ _ positive).mp present, rfl⟩
  · rintro ⟨direction, member, r, c, valid, rfl⟩
    exact ⟨direction, member, (r, c), (mem_starts_iff _ _ _ _ _ _ positive).mpr valid, rfl⟩

/-- The directional reference enumerates at least one empty product, even if
one of the grid dimensions is zero. -/
theorem maximum_directional_zero (grid : List (List Nat)) (rows columns : Nat) :
    (directionalProducts grid rows columns 0).foldl max 0 = 1 := by
  have same (value : Nat) : value ∈ directionalProducts grid rows columns 0 ↔ value ∈ [1] := by
    simp only [directionalProducts, List.mem_flatMap, List.mem_map, List.mem_singleton]
    constructor
    · rintro ⟨direction, _, ⟨r, c⟩, _, rfl⟩
      rfl
    · rintro rfl
      refine ⟨.downRight, by simp [directions], (0, 0), ?_, rfl⟩
      simp [starts]
  simpa using ListMaximum.eq_of_same_members (directionalProducts grid rows columns 0) [1] 0 same

/-- A rectangle with two rows and a column contains a valid empty-product
endpoint check in the downward direction. -/
theorem maximum_scanned_zero (grid : List (List Nat)) (rows columns : Nat)
    (twoRows : 2 ≤ rows) (oneColumn : 0 < columns) :
    (scannedProducts grid rows columns 0).foldl max 0 = 1 := by
  have same (value : Nat) : value ∈ scannedProducts grid rows columns 0 ↔ value ∈ [1] := by
    rw [mem_scannedProducts_iff]
    simp only [List.mem_singleton]
    constructor
    · rintro ⟨direction, _, r, c, _, rfl⟩
      rfl
    · rintro rfl
      refine ⟨.down, by simp [directions], 1, 0, ?_, rfl⟩
      simp only [ValidStart, Direction.rowStep, Direction.columnStep]
      omega
  simpa using ListMaximum.eq_of_same_members (scannedProducts grid rows columns 0) [1] 0 same

end ProjectEulerStatements.Grid
