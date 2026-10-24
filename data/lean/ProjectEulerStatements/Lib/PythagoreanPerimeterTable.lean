import ProjectEulerStatements.Lib.PythagoreanPerimeterCounting

/-! Each table update counts one Euclid parameter tuple, preserving the source loop order. -/
namespace ProjectEulerStatements.PythagoreanPerimeterCounting

set_option Elab.async false

abbrev ParameterTuple := Nat × Nat × Nat

def multipleParameters (m n first count : Nat) : List ParameterTuple :=
  (List.range' first count).map (fun k => (m, n, k))

def rowParameters (limit m first count : Nat) : List ParameterTuple :=
  (List.range' first count).flatMap (fun n =>
    if permitted limit m n then multipleParameters m n 1 (limit / perimeter m n) else [])

def outerParameters (limit first count : Nat) : List ParameterTuple :=
  (List.range' first count).flatMap (fun m =>
    if 2 * m * (m + 1) ≤ limit then rowParameters limit m 1 (m - 1) else [])

/-- Counting at a perimeter does not deduplicate tuples: uniqueness is proved separately. -/
def matching (p : Nat) (items : List ParameterTuple) : Nat :=
  (items.filter (fun t => decide (p = t.2.2 * perimeter t.1 t.2.1))).length

@[simp] theorem matching_nil (p : Nat) : matching p [] = 0 := rfl

theorem matching_cons (p : Nat) (item : ParameterTuple) (items : List ParameterTuple) :
    matching p (item :: items) =
      (if p = item.2.2 * perimeter item.1 item.2.1 then 1 else 0) + matching p items := by
  simp [matching, List.filter_cons]
  split <;> simp [Nat.add_comm]

@[simp] theorem matching_append (p : Nat) (left right : List ParameterTuple) :
    matching p (left ++ right) = matching p left + matching p right := by
  simp [matching, List.filter_append]

theorem addMultiples_count (limit m n first count : Nat) (table : Table) (p : Nat) :
    addMultiples limit m n first count table p =
      table p + matching p (multipleParameters m n first count) := by
  induction count generalizing first table with
  | zero => simp [addMultiples, multipleParameters]
  | succ count ih =>
      rw [addMultiples_step, ih]
      have expansion : multipleParameters m n first (count + 1) =
          (m, n, first) :: multipleParameters m n (first + 1) count := by
        simp [multipleParameters, List.range'_succ]
      rw [expansion, matching_cons]
      by_cases same : p = first * perimeter m n <;> simp [increment, same, Nat.add_assoc]

theorem row_count (limit m first count : Nat) (table : Table) (p : Nat) :
    row limit m first count table p =
      table p + matching p (rowParameters limit m first count) := by
  induction count generalizing first table with
  | zero => simp [row, rowParameters]
  | succ count ih =>
      rw [row_step, ih]
      have expansion : rowParameters limit m first (count + 1) =
          (if permitted limit m first then
            multipleParameters m first 1 (limit / perimeter m first)
            else []) ++ rowParameters limit m (first + 1) count := by
        simp [rowParameters, List.range'_succ]
      rw [expansion, matching_append]
      cases permitted limit m first <;> simp [addMultiples_count, Nat.add_assoc]

theorem outer_count (limit first count : Nat) (table : Table) (p : Nat) :
    outer limit first count table p =
      table p + matching p (outerParameters limit first count) := by
  induction count generalizing first table with
  | zero => simp [outer, outerParameters]
  | succ count ih =>
      rw [outer_step, ih]
      have expansion : outerParameters limit first (count + 1) =
          (if 2 * first * (first + 1) ≤ limit then rowParameters limit first 1 (first - 1)
            else []) ++ outerParameters limit (first + 1) count := by
        simp [outerParameters, List.range'_succ]
      rw [expansion, matching_append]
      by_cases active : 2 * first * (first + 1) ≤ limit <;>
        simp [active, row_count, Nat.add_assoc]

theorem table_count (limit p : Nat) :
    table limit p = matching p (outerParameters limit 2 (limit - 1)) := by
  simp [table, outer_count]

end ProjectEulerStatements.PythagoreanPerimeterCounting
