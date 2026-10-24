import ProjectEulerStatements.Lib.DoublePalindromes
import ProjectEulerStatements.Lib.DecimalDigits

/-! Binary formatting and palindrome recognition on arbitrary positive inputs. -/
namespace ProjectEulerStatements.DoublePalindromes

set_option Elab.async false

theorem toDigits_eq_digitChars (base n : Nat) (baseBound : 2 ≤ base) (positive : 0 < n) :
    Nat.toDigits base n = (Nat.digits base n).reverse.map Nat.digitChar := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases small : n < base
      · rw [Nat.toDigits_of_lt_base small,
          Nat.digits_of_lt base n (Nat.ne_of_gt positive) small]
        simp
      · have large : base ≤ n := by omega
        have quotientPositive : 0 < n / base := Nat.div_pos large (by omega)
        have quotientSmaller : n / base < n := Nat.div_lt_self positive (by omega)
        have remainderBound : n % base < base := Nat.mod_lt n (by omega)
        have decomposition : n = base * (n / base) + n % base := by
          conv_lhs => rw [← Nat.div_add_mod n base]
        calc
          Nat.toDigits base n = Nat.toDigits base (base * (n / base) + n % base) :=
            congrArg (Nat.toDigits base) decomposition
          _ = Nat.toDigits base (n / base) ++ Nat.toDigits base (n % base) :=
            (Nat.toDigits_append_toDigits (b := base) (n := n / base) (d := n % base)
              (by omega) quotientPositive remainderBound).symm
          _ = (Nat.digits base (n / base)).reverse.map Nat.digitChar ++
                [Nat.digitChar (n % base)] := by
            rw [ih (n / base) quotientSmaller quotientPositive,
              Nat.toDigits_of_lt_base remainderBound]
          _ = (Nat.digits base n).reverse.map Nat.digitChar := by
            rw [Nat.digits_of_two_le_of_pos baseBound positive]
            simp [List.map_append]

theorem binary_toDigits (n : Nat) (positive : 0 < n) :
    Nat.toDigits 2 n = (Nat.digits 2 n).reverse.map Nat.digitChar :=
  toDigits_eq_digitChars 2 n (by decide) positive

private theorem decode_digitChars (digits : List Nat)
    (bounds : ∀ digit ∈ digits, digit < 10) :
    (digits.map Nat.digitChar).map (fun c => c.toNat - '0'.toNat) = digits := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id digits]
  apply List.map_congr_left
  intro digit member
  exact DecimalDigits.digitChar_val digit (bounds digit member)

theorem binary_string_palindrome (n : Nat) :
    decide (Nat.toDigits 2 n = (Nat.toDigits 2 n).reverse) =
      P36.isPalindromeBase 2 n := by
  by_cases zero : n = 0
  · subst n
    decide +kernel
  · have positive : 0 < n := by omega
    have bounds : ∀ digit ∈ Nat.digits 2 n, digit < 10 := by
      intro digit member
      have binary := Nat.digits_lt_base (by decide : 1 < 2) member
      omega
    rw [binary_toDigits n positive, ← List.map_reverse, List.reverse_reverse]
    unfold P36.isPalindromeBase
    apply decide_eq_decide.mpr
    constructor
    · intro equal
      have decoded := congrArg (List.map (fun c : Char => c.toNat - '0'.toNat)) equal
      rw [decode_digitChars _ (fun digit member => bounds digit (List.mem_reverse.mp member)),
        decode_digitChars _ bounds] at decoded
      exact decoded.symm
    · intro equal
      exact congrArg (List.map Nat.digitChar) equal.symm

theorem positive_palindrome_bitand (n : Nat) (positive : 0 < n)
    (palindrome : P36.isPalindromeBase 2 n = true) : n &&& 1 = 1 := by
  simpa using palindrome_positive_odd n positive palindrome

end ProjectEulerStatements.DoublePalindromes
