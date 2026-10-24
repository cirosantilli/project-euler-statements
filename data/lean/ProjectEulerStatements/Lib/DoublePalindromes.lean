import ProjectEulerStatements.P36
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Digits.Lemmas
import Lean.Elab.Tactic.Omega

/-! Reference sums and the exact odd/even decimal seed enumeration used by
the Python solver. Enumeration completeness is proved in subsequent modules. -/
namespace ProjectEulerStatements.DoublePalindromes

set_option Elab.async false

theorem fold_filter_sum (items : List Nat) (predicate : Nat → Bool) (initial : Nat) :
    items.foldl (fun total n => if predicate n then total + n else total) initial =
      initial + (items.filter predicate).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      cases selected : predicate head <;>
        simp [List.foldl, List.filter, selected, ih, Nat.add_assoc]

theorem naive_filter_sum (limit : Nat) :
    P36.naive limit = ((List.range limit).filter P36.isDoublePalindrome).sum := by
  have same : ((List.range limit).filter P36.isDoublePalindrome).toFinset =
      (Finset.range limit).filter (fun n => P36.isDoublePalindrome n) := by
    ext n
    simp
  unfold P36.naive P36.sumDoublePalindromes
  rw [← same, List.sum_toFinset]
  · simp
  · exact List.Nodup.filter _ List.nodup_range

theorem naive_fold (limit : Nat) :
    P36.naive limit = (List.range limit).foldl
      (fun total n => if P36.isDoublePalindrome n then total + n else total) 0 := by
  simp [fold_filter_sum, naive_filter_sum]

@[simp] theorem zero_double_palindrome : P36.isDoublePalindrome 0 = true := by
  simp [P36.isDoublePalindrome, P36.isPalindromeBase]

/-- Zero is accepted by the reference but contributes nothing to its sum. -/
theorem filter_sum_without_zero (items : List Nat) :
    (items.filter P36.isDoublePalindrome).sum =
      (items.filter (fun n => decide (0 < n) && P36.isDoublePalindrome n)).sum := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | zero => simpa using ih
      | succ head =>
          cases accepted : P36.isDoublePalindrome (head + 1) <;>
            simp [List.filter, accepted, ih]

theorem palindrome_positive_odd (n : Nat) (positive : 0 < n)
    (palindrome : P36.isPalindromeBase 2 n = true) : n % 2 = 1 := by
  have nonempty : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have reversed : (Nat.digits 2 n).reverse = Nat.digits 2 n := by
    exact (of_decide_eq_true palindrome).symm
  have nonzero := Nat.getLast_digit_ne_zero 2 (show n ≠ 0 by omega)
  simp only [List.getLast_eq_head_reverse, reversed] at nonzero
  have first : (Nat.digits 2 n).head nonempty = n % 2 := by
    simp only [Nat.digits_def' (b := 2) (by decide) positive, List.head_cons]
  rw [first] at nonzero
  have bound := Nat.mod_lt n (by decide : 0 < 2)
  omega

def decimalDigits (seed : Nat) : List Nat := (Nat.digits 10 seed).reverse

def oddDigits (seed : Nat) : List Nat :=
  decimalDigits seed ++ (decimalDigits seed).dropLast.reverse

def evenDigits (seed : Nat) : List Nat :=
  decimalDigits seed ++ (decimalDigits seed).reverse

def oddPalindrome (seed : Nat) : Nat := Nat.ofDigits 10 (oddDigits seed).reverse

def evenPalindrome (seed : Nat) : Nat := Nat.ofDigits 10 (evenDigits seed).reverse

def candidates : List Nat :=
  (List.range' 1 999).flatMap (fun seed => [oddPalindrome seed, evenPalindrome seed])

def generate (limit : Nat) : List Nat := candidates.filter (fun n => decide (n < limit))

end ProjectEulerStatements.DoublePalindromes
