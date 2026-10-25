import ProjectEulerStatements.Lib.BoundedOrbit
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Digit growth gives a finite invariant interval for every starting value. -/
namespace ProjectEulerStatements.DigitFactorialChains
set_option Elab.async false

def nextTerm (n : Nat) : Nat :=
  if n = 0 then 1 else ((Nat.digits 10 n).map Nat.factorial).sum

def threshold : Nat := 7 * Nat.factorial 9
def bound (start : Nat) : Nat := max start threshold

@[simp] theorem nextTerm_zero : nextTerm 0 = 1 := by simp [nextTerm]

theorem nextTerm_step (n : Nat) (positive : 0 < n) :
    nextTerm n = Nat.factorial (n % 10) +
      (if n / 10 = 0 then 0 else nextTerm (n / 10)) := by
  rw [nextTerm, if_neg (by omega), Nat.digits_def' (by decide) positive,
    List.map_cons, List.sum_cons]
  by_cases zero : n / 10 = 0 <;> simp [zero, nextTerm]

theorem sum_le (digits : List Nat) (small : ∀ digit ∈ digits, digit < 10) :
    (digits.map Nat.factorial).sum ≤ digits.length * Nat.factorial 9 := by
  induction digits with
  | nil => simp
  | cons digit rest ih =>
      have headBound := Nat.factorial_le (show digit ≤ 9 by have := small digit (by simp); omega)
      have tail := ih (fun n member => small n (by simp [member]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

private theorem bad_succ (digits : Nat) (positive : 1 ≤ digits)
    (bad : digits * Nat.factorial 9 < 10 ^ (digits - 1)) :
    (digits + 1) * Nat.factorial 9 < 10 ^ digits := by
  calc
    (digits + 1) * Nat.factorial 9 ≤ (10 * digits) * Nat.factorial 9 :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 10 * (digits * Nat.factorial 9) := by ring
    _ < 10 * 10 ^ (digits - 1) := Nat.mul_lt_mul_of_pos_left bad (by decide)
    _ = 10 ^ digits := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
      congr 1
      omega

/-- From eight digits onward, place values exceed every possible digit-factorial sum. -/
theorem wide_sum_lt (digits : Nat) (wide : 8 ≤ digits) :
    digits * Nat.factorial 9 < 10 ^ (digits - 1) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le wide
  clear wide
  induction extra with
  | zero => decide
  | succ extra ih =>
      simpa only [Nat.add_assoc, Nat.add_sub_cancel] using
        bad_succ (8 + extra) (by omega) ih

/-- Small inputs enter the invariant interval; larger inputs cannot increase. -/
theorem nextTerm_le (n : Nat) : nextTerm n ≤ max n threshold := by
  by_cases zero : n = 0
  · subst n
    have positive := Nat.factorial_pos 9
    simp only [nextTerm_zero, Nat.zero_max, threshold]
    omega
  · let digits := (Nat.digits 10 n).length
    have estimate := sum_le (Nat.digits 10 n)
      (fun digit member => Nat.digits_lt_base (by decide) member)
    rw [nextTerm, if_neg zero]
    by_cases short : digits ≤ 7
    · exact (estimate.trans (Nat.mul_le_mul_right _ short)).trans (le_max_right _ _)
    · have wide := wide_sum_lt digits (by omega)
      have lower : 10 ^ (digits - 1) ≤ n :=
        (Nat.lt_digits_length_iff (by decide : 1 < 10) n).mp (by
          change digits - 1 < digits
          omega)
      exact (estimate.trans (wide.le.trans lower)).trans (le_max_left _ _)

theorem nextTerm_bounded (start n : Nat) (inside : n ≤ bound start) :
    nextTerm n ≤ bound start := by
  apply (nextTerm_le n).trans
  exact max_le inside (le_max_right _ _)

def path (start : Nat) : List Nat :=
  BoundedOrbit.walk nextTerm (bound start) (nextTerm_bounded start)
    start [] (le_max_left _ _) (by simp) (by simp [BoundedOrbit.Within])

theorem path_trace (start : Nat) : BoundedOrbit.Trace nextTerm start [] (path start) :=
  BoundedOrbit.walk_trace nextTerm (bound start) (nextTerm_bounded start)
    start [] (le_max_left _ _) (by simp) (by simp [BoundedOrbit.Within])

theorem path_distinct (start : Nat) : (path start).Nodup :=
  (path_trace start).distinct (by simp)

theorem path_mem_iff (start n : Nat) :
    n ∈ path start ↔ ∃ steps : Nat, nextTerm^[steps] start = n :=
  (path_trace start).mem_iff

def chainLen (start : Nat) : Nat := (path start).length

theorem chainLen_of_trace (start : Nat) (result : List Nat)
    (trace : BoundedOrbit.Trace nextTerm start [] result) : chainLen start = result.length := by
  exact congrArg List.length ((path_trace start).unique trace)

theorem chainLen_positive (start : Nat) : 0 < chainLen start := by
  have member := (path_trace start).current_mem
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem member)

end ProjectEulerStatements.DigitFactorialChains
