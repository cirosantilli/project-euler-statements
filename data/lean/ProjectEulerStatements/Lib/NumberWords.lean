import ProjectEulerStatements.P17
import Mathlib.Tactic

/-! Decimal groups and British number-word lengths. -/
namespace ProjectEulerStatements.P17

/-- The three irregular word tables used to spell positive numbers below 100. -/
def onesWords : List String :=
  ["", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def teenWords : List String :=
  ["ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen",
    "seventeen", "eighteen", "nineteen"]

def tensWords : List String :=
  ["twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety"]

theorem onesWords_length (n : Nat) (bound : n < 10) :
    onesWords[n]!.length = smallWordLen n := by
  interval_cases n <;> decide

theorem teenWords_length (n : Nat) (lower : 10 ≤ n) (upper : n < 20) :
    teenWords[n - 10]!.length = smallWordLen n := by
  interval_cases n <;> decide

theorem tensWords_length (n : Nat) (lower : 2 ≤ n) (upper : n < 10) :
    tensWords[n - 2]!.length = tensWordLen n := by
  interval_cases n <;> decide

@[simp] theorem wordLen_zero : wordLen 0 = 0 := by rw [wordLen]; rfl

/-- Counting from one or from zero gives the same total. -/
theorem sum_wordLen (n : Nat) : ((List.range' 1 n).map wordLen).sum = naive n := by
  have total : ((List.range (n + 1)).map wordLen).sum = naive n := by
    rw [List.sum_eq_foldl, List.foldl_map]
    rfl
  rw [List.range_eq_range', List.range'_succ] at total
  simpa using total

/-- The first twenty lengths form the irregular part of English number names. -/
theorem wordLen_below_twenty (n : Nat) (bound : n < 20) : wordLen n = smallWordLen n := by
  by_cases zero : n = 0
  · subst n
    rw [wordLen_zero]
    rfl
  · rw [wordLen, if_neg zero, if_pos bound]

theorem wordLen_below_hundred (n : Nat) (bound : n < 100) :
    wordLen n = if n < 20 then smallWordLen n else
      tensWordLen (n / 10) + smallWordLen (n % 10) := by
  by_cases small : n < 20
  · rw [if_pos small, wordLen_below_twenty n small]
  · rw [if_neg small, wordLen, if_neg (by omega), if_neg small, if_pos bound]

/-- British "and" occurs precisely when a hundreds group has a nonzero remainder. -/
theorem wordLen_hundreds (n : Nat) (lower : 100 ≤ n) (upper : n < 1000) :
    wordLen n = smallWordLen (n / 100) + 7 +
      (if n % 100 = 0 then 0 else 3 + wordLen (n % 100)) := by
  rw [wordLen, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos upper]

@[simp] theorem wordLen_thousand : wordLen 1000 = 11 := by rw [wordLen]; rfl

/-- The reference deliberately assigns zero outside its English-name domain. -/
theorem wordLen_above_thousand (n : Nat) (lower : 1000 < n) : wordLen n = 0 := by
  rw [wordLen, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

end ProjectEulerStatements.P17
