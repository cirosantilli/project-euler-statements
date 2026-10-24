import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Range

/-! Left-to-right maximum selection, retaining the first element on equal scores. -/
namespace ProjectEulerStatements.ArgMaximum

variable {α β : Type*} [Preorder β] [DecidableLT β]

def select (score : α → β) (best candidate : α) : α :=
  if score best < score candidate then candidate else best

theorem fold_some (score : α → β) (items : List α) (initial : α) :
    items.foldl (List.argAux (fun candidate best => score best < score candidate)) (some initial) =
      some (items.foldl (select score) initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [List.foldl_cons, List.argAux, select]
      split <;> exact ih _

theorem argmax_cons (score : α → β) (initial : α) (items : List α) :
    List.argmax score (initial :: items) = some (items.foldl (select score) initial) := by
  simpa only [List.argmax, List.foldl_cons, List.argAux] using fold_some score items initial

theorem argmax_range_succ (score : Nat → β) (n : Nat) :
    List.argmax score (List.range (n + 1)) = some ((List.range' 1 n).foldl (select score) 0) := by
  rw [List.range_eq_range', List.range'_succ]
  exact argmax_cons score 0 _

end ProjectEulerStatements.ArgMaximum
