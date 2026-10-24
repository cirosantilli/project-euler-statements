import Mathlib.Data.List.MinMax

/-! Maximum folds depend on the values encountered, not their order or repetition. -/
namespace ProjectEulerStatements.ListMaximum

variable {α : Type*} [LinearOrder α]

theorem fold_le_iff (items : List α) (initial bound : α) :
    items.foldl max initial ≤ bound ↔ initial ≤ bound ∧ ∀ value ∈ items, value ≤ bound := by
  induction items generalizing initial with
  | nil => simp
  | cons value rest ih => simp [List.foldl_cons, ih, and_assoc, and_left_comm, and_comm]

theorem le_fold_of_mem (items : List α) (initial value : α) (member : value ∈ items) :
    value ≤ items.foldl max initial :=
  ((fold_le_iff items initial _).mp le_rfl).2 value member

/-- Reordering or duplicating candidates does not change a maximum search. -/
theorem eq_of_same_members (left right : List α) (initial : α)
    (same : ∀ value, value ∈ left ↔ value ∈ right) :
    left.foldl max initial = right.foldl max initial := by
  apply le_antisymm
  · apply (fold_le_iff left initial _).mpr
    exact ⟨((fold_le_iff right initial _).mp le_rfl).1,
      fun value member => le_fold_of_mem right initial value ((same value).mp member)⟩
  · apply (fold_le_iff right initial _).mpr
    exact ⟨((fold_le_iff left initial _).mp le_rfl).1,
      fun value member => le_fold_of_mem left initial value ((same value).mpr member)⟩

/-- A function that preserves maxima commutes with a maximum fold. -/
theorem fold_map {β : Type*} [LinearOrder β] (f : α → β)
    (preserves : ∀ a b, f (max a b) = max (f a) (f b)) (items : List α) (initial : α) :
    (items.map f).foldl max (f initial) = f (items.foldl max initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons value rest ih =>
      simpa only [List.map_cons, List.foldl_cons, ← preserves] using ih (max initial value)

end ProjectEulerStatements.ListMaximum
