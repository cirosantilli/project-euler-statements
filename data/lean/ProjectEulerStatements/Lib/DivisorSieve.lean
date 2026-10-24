import ProjectEulerStatements.P21
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

/-! Partial divisor sums and the updates made by the proper-divisor sieve. -/
namespace ProjectEulerStatements.DivisorSieve

/-- A proper divisor cannot exceed half its positive multiple. -/
theorem twice_le (d n : Nat) (proper : d < n) (divides : d ∣ n) : 2 * d ≤ n := by
  have difference : d ∣ n - d := Nat.dvd_sub divides (dvd_refl d)
  have bound := Nat.le_of_dvd (by omega : 0 < n - d) difference
  omega

/-- Sum the proper divisors already visited by the outer loop. -/
def sumsBefore (next n : Nat) : Nat :=
  ∑ d ∈ Finset.range next, if 0 < d ∧ d < n ∧ d ∣ n then d else 0

@[simp] theorem sumsBefore_one (n : Nat) : sumsBefore 1 n = 0 := by
  simp [sumsBefore]

theorem sumsBefore_step (i n : Nat) (positive : 0 < i) :
    sumsBefore (i + 1) n = sumsBefore i n + if 2 * i ≤ n ∧ i ∣ n then i else 0 := by
  have proper : (0 < i ∧ i < n ∧ i ∣ n) ↔ (2 * i ≤ n ∧ i ∣ n) := by
    constructor
    · rintro ⟨_, smaller, divides⟩
      exact ⟨twice_le i n smaller divides, divides⟩
    · rintro ⟨bound, divides⟩
      exact ⟨positive, by omega, divides⟩
  simp only [sumsBefore, Finset.sum_range_succ, proper]

/-- A prefix beyond half the input contains every proper divisor. -/
theorem sumsBefore_complete (cutoff n : Nat) (enough : n / 2 < cutoff) :
    sumsBefore cutoff n = P21.d n := by
  have same : (Finset.range cutoff).filter (fun d => 0 < d ∧ d < n ∧ d ∣ n) =
      P21.properDivisors n := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, P21.properDivisors, Finset.mem_Icc]
    constructor
    · rintro ⟨_, positive, proper, divides⟩
      exact ⟨⟨by omega, by omega⟩, divides⟩
    · rintro ⟨⟨positive, proper⟩, divides⟩
      have smaller : d < n := by omega
      have half := twice_le d n smaller divides
      exact ⟨by omega, by omega, smaller, divides⟩
  simpa only [sumsBefore, P21.d, Finset.sum_filter] using
    congrArg (fun s : Finset Nat => ∑ d ∈ s, d) same

/-- A sumsBeforely completed inner pass has updated precisely its earlier multiples. -/
def row (base : Nat → Nat) (i next n : Nat) : Nat :=
  base n + if 2 * i ≤ n ∧ n < next ∧ i ∣ n then i else 0

@[simp] theorem row_start (base : Nat → Nat) (i n : Nat) : row base i (2 * i) n = base n := by
  simp [row, show ¬ (2 * i ≤ n ∧ n < 2 * i ∧ i ∣ n) by omega]

/-- No other multiple lies between a multiple and the next one. -/
theorem consecutive (i j n : Nat) (atMultiple : i ∣ j) (divides : i ∣ n)
    (lower : j ≤ n) (upper : n < j + i) : n = j := by
  by_contra different
  have difference : i ∣ n - j := Nat.dvd_sub divides atMultiple
  have bound := Nat.le_of_dvd (by omega : 0 < n - j) difference
  omega

theorem row_step (base : Nat → Nat) (i j n : Nat) (positive : 0 < i)
    (lower : 2 * i ≤ j) (multiple : i ∣ j) :
    row base i (j + i) n = if n = j then row base i j n + i else row base i j n := by
  by_cases same : n = j
  · subst n
    simp [row, lower, multiple, positive]
  · by_cases before : n < j
    · have smaller : n < j + i := by omega
      simp [row, same, before, smaller]
    · have after : ¬ (2 * i ≤ n ∧ n < j + i ∧ i ∣ n) := by
        rintro ⟨_, upper, divides⟩
        exact same (consecutive i j n multiple divides (by omega) upper)
      simp [row, same, before, after]

theorem row_complete (i next n : Nat) (positive : 0 < i) (finished : n < next) :
    row (sumsBefore i) i next n = sumsBefore (i + 1) n := by
  simp [row, finished, sumsBefore_step i n positive]

end ProjectEulerStatements.DivisorSieve
