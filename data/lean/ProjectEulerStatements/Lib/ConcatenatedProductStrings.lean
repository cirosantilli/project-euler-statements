import ProjectEulerStatements.Lib.ConcatenatedProducts
import Init.Data.String.Lemmas.Intercalate

/-! The source's string list and join agree with positional decimal concatenation. -/
namespace ProjectEulerStatements.ConcatenatedProducts

open P38

def parts (n k : Nat) : List String :=
  (List.range k).map (fun i => toString ((n * (i + 1) : Nat) : Int))

def text (n k : Nat) : String := String.join (parts n k)

theorem parts_zero (n : Nat) : parts n 0 = [] := rfl

theorem parts_succ (n k : Nat) :
    parts n (k + 1) = parts n k ++ [toString ((n * (k + 1) : Nat) : Int)] := by
  simp [parts, List.range_succ]

theorem text_zero (n : Nat) : text n 0 = "" := rfl

theorem text_succ (n k : Nat) :
    text n (k + 1) = text n k ++ toString ((n * (k + 1) : Nat) : Int) := by
  apply String.toList_injective
  simp [text, parts_succ]

theorem intercalate_parts (n k : Nat) : "".intercalate (parts n k) = text n k := by
  unfold text
  generalize parts n k = items
  induction items with
  | nil => rfl
  | cons head tail ih => cases tail <;> simp_all

theorem decimal_characters (n : Nat) (positive : 0 < n) :
    (toString (n : Int)).toList = (digitsBE n).map Nat.digitChar := by
  simpa [toString, Int.repr, Nat.repr, digitsBE] using
    DecimalDigits.toDigits_eq_digitChars n positive

theorem text_characters (n k : Nat) (positive : 0 < n) :
    (text n k).toList = (digitsBE (concatProduct n k)).map Nat.digitChar := by
  induction k with
  | zero => simp [text_zero, concatProduct_zero, digitsBE]
  | succ k ih =>
      rw [text_succ, String.toList_append, ih,
        decimal_characters _ (Nat.mul_pos positive (by omega)), concatProduct_digits_succ]
      simp only [List.map_append]

theorem text_length (n k : Nat) (positive : 0 < n) :
    (text n k).toList.length = numDigits (concatProduct n k) := by
  simp only [text_characters n k positive, List.length_map, digitsBE,
    List.length_reverse, numDigits]

theorem parts_length_sum (n k : Nat) (positive : 0 < n) :
    ((parts n k).map (fun s => s.toList.length)).sum = numDigits (concatProduct n k) := by
  induction k with
  | zero => simp [parts_zero, concatProduct_zero, numDigits]
  | succ k ih =>
      rw [parts_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [concatProduct_length_succ,
        DecimalDigits.int_string_length (n * (k + 1)) (Nat.mul_pos positive (by omega))]
      rfl

theorem concatProduct_positive (n k : Nat) (positive : 0 < n) (nonzero : 0 < k) :
    0 < concatProduct n k := by
  have length := concatProduct_length_lower n k positive
  by_contra h
  have zero : concatProduct n k = 0 := by omega
  simp [zero, numDigits] at length
  omega

theorem text_decimal (n k : Nat) (positive : 0 < n) (nonzero : 0 < k) :
    text n k = toString (concatProduct n k : Int) := by
  apply String.toList_injective
  rw [text_characters n k positive,
    decimal_characters _ (concatProduct_positive n k positive nonzero)]

end ProjectEulerStatements.ConcatenatedProducts
