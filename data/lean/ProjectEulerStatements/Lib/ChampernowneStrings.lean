import ProjectEulerStatements.P40
import ProjectEulerStatements.Lib.DecimalDigits
import Mathlib.Data.List.GetD

/-! Decimal indexing for the actual `int(str(num)[pos])` operation in problem 40. -/
namespace ProjectEulerStatements.ChampernowneStrings

set_option Elab.async false

open ProjectEulerStatements

theorem int_characters (n : Nat) (positive : 0 < n) :
    (toString (n : Int)).toList = (P40.digitsBE n).map Nat.digitChar := by
  simpa [toString, Int.repr, Nat.repr, P40.digitsBE] using
    DecimalDigits.toDigits_eq_digitChars n positive

theorem digit_lt (n index : Nat) (bounded : index < (P40.digitsBE n).length) :
    (P40.digitsBE n).getD index 0 < 10 := by
  rw [List.getD_eq_getElem _ _ bounded]
  apply Nat.digits_lt_base (b := 10) (m := n) (by decide)
  exact List.mem_reverse.mp (List.getElem_mem (l := P40.digitsBE n) bounded)

theorem int_character (n index : Nat) (positive : 0 < n)
    (bounded : index < (P40.digitsBE n).length) :
    (toString (n : Int)).toList[index]? =
      some (Nat.digitChar ((P40.digitsBE n).getD index 0)) := by
  rw [int_characters n positive, List.getElem?_map]
  rw [List.getElem?_eq_getElem bounded, List.getD_eq_getElem _ _ bounded]
  rfl

theorem digit_string (digit : Nat) (bounded : digit < 10) :
    String.ofList [Nat.digitChar digit] = toString digit := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toDigits_of_lt_base bounded]

theorem indexed_digit_string (n index : Nat) (bounded : index < (P40.digitsBE n).length) :
    String.ofList [Nat.digitChar ((P40.digitsBE n).getD index 0)] =
      toString ((P40.digitsBE n).getD index 0) :=
  digit_string _ (digit_lt n index bounded)

end ProjectEulerStatements.ChampernowneStrings
