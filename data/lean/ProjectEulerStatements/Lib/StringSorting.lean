import lang.py.FormalSW.ScalarSort
import Mathlib.Data.List.Sort
import Mathlib.Data.String.Basic

/-! The interpreter's string sort agrees with Mathlib's lexicographic string order. -/
namespace ProjectEulerStatements.StringSorting
open FormalSW.PyAst
set_option Elab.async false

/-- Mathlib replaces the core string order; the interpreter retains the original instance. -/
theorem comparison (a b : String) : @LT.lt String String.instLT a b ↔ a < b :=
  String.lt_iff.trans ((List.lt_iff_lex_lt _ _).trans String.lt_iff_toList_lt.symm)

theorem insert_ordered (value : String) (items : List String)
    (ordered : items.Pairwise (· ≤ ·)) :
    (ScalarSort.insertString value items).Pairwise (· ≤ ·) := by
  induction items with
  | nil => simp [ScalarSort.insertString]
  | cons first rest ih =>
      obtain ⟨lower, tailOrdered⟩ := List.pairwise_cons.mp ordered
      by_cases smaller : first < value
      · simp only [ScalarSort.insertString, if_pos ((comparison first value).mpr smaller),
          List.pairwise_cons]
        refine ⟨?_, ih tailOrdered⟩
        intro item member
        have member := (ScalarSort.insertString_perm value rest).mem_iff.mp member
        rcases List.mem_cons.mp member with rfl | member
        · exact le_of_lt smaller
        · exact lower item member
      · simp only [ScalarSort.insertString, if_neg ((comparison first value).not.mpr smaller),
          List.pairwise_cons]
        refine ⟨?_, lower, tailOrdered⟩
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact le_of_not_gt smaller
        · exact le_trans (le_of_not_gt smaller) (lower item member)

theorem strings_ordered (items : List String) :
    (ScalarSort.strings items).Pairwise (· ≤ ·) := by
  induction items with
  | nil => exact .nil
  | cons first rest ih => exact insert_ordered first (ScalarSort.strings rest) ih

end ProjectEulerStatements.StringSorting
