import ProjectEulerStatements.P26
import Mathlib.NumberTheory.PowModTotient

/-! Finite multiplicative periods justify the source's unbounded remainder search. -/
namespace ProjectEulerStatements.RecurringCycle
open P26

private theorem stripFactor_spec (p n : Nat) (hp : 1 < p) (hn : 0 < n) :
    0 < stripFactor p n ∧ stripFactor p n ∣ n ∧ ¬ p ∣ stripFactor p n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [stripFactor]
      simp only [show ¬ p ≤ 1 by omega, show n ≠ 0 by omega, ↓reduceDIte]
      by_cases divisible : n % p = 0
      · rw [if_pos divisible]
        have divides : p ∣ n := Nat.dvd_of_mod_eq_zero divisible
        have smaller : n / p < n := Nat.div_lt_self hn hp
        have positive : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn divides) (by omega)
        obtain ⟨positive, dividesResult, indivisible⟩ := ih (n / p) smaller positive
        exact ⟨positive, dividesResult.trans (Nat.div_dvd_of_dvd divides), indivisible⟩
      · rw [if_neg divisible]
        exact ⟨hn, dvd_rfl, fun divides => divisible (Nat.mod_eq_zero_of_dvd divides)⟩

theorem stripFactor_pos (p n : Nat) (hp : 1 < p) (hn : 0 < n) :
    0 < stripFactor p n := (stripFactor_spec p n hp hn).1

theorem stripFactor_dvd (p n : Nat) (hp : 1 < p) (hn : 0 < n) :
    stripFactor p n ∣ n := (stripFactor_spec p n hp hn).2.1

theorem stripFactor_not_dvd (p n : Nat) (hp : 1 < p) (hn : 0 < n) :
    ¬ p ∣ stripFactor p n := (stripFactor_spec p n hp hn).2.2

theorem stripFactor_step (p n : Nat) (hp : 1 < p) (hn : 0 < n) (divisible : n % p = 0) :
    stripFactor p n = stripFactor p (n / p) := by
  rw [stripFactor]
  simp [show ¬ p ≤ 1 by omega, show n ≠ 0 by omega, divisible]

theorem stripFactor_done (p n : Nat) (hp : 1 < p) (indivisible : n % p ≠ 0) :
    stripFactor p n = n := by
  rw [stripFactor]
  simp only [show ¬ p ≤ 1 by omega, ↓reduceDIte, indivisible, ↓reduceIte]
  split <;> simp_all

theorem reducedDenom_pos (d : Nat) (positive : 0 < d) : 0 < reducedDenom d :=
  stripFactor_pos 5 _ (by decide) (stripFactor_pos 2 d (by decide) positive)

theorem reducedDenom_coprime (d : Nat) (positive : 0 < d) : Nat.Coprime 10 (reducedDenom d) := by
  have positive2 := stripFactor_pos 2 d (by decide) positive
  have two : ¬ 2 ∣ reducedDenom d := by
    intro divides
    exact stripFactor_not_dvd 2 d (by decide) positive
      (divides.trans (stripFactor_dvd 5 _ (by decide) positive2))
  have five : ¬ 5 ∣ reducedDenom d := stripFactor_not_dvd 5 _ (by decide) positive2
  have c2 : Nat.Coprime 2 (reducedDenom d) := (Nat.prime_two.coprime_iff_not_dvd).mpr two
  have c5 : Nat.Coprime 5 (reducedDenom d) := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr five
  exact c2.mul_left c5

private theorem exists_period (d : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d) :
    ∃ k : Nat, 0 < k ∧ 10 ^ k % d = 1 :=
  ⟨d.totient, Nat.totient_pos.mpr (by omega), Nat.pow_totient_mod_eq_one large coprime⟩

/-- The least positive power returning remainder one, or zero outside the search domain. -/
noncomputable def first (d : Nat) : Nat :=
  if valid : 1 < d ∧ Nat.Coprime 10 d then Nat.find (exists_period d valid.1 valid.2) else 0

private theorem first_eq_find (d : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d) :
    first d = Nat.find (exists_period d large coprime) := by
  rw [first, dif_pos ⟨large, coprime⟩]

theorem first_pos (d : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d) : 0 < first d := by
  rw [first_eq_find d large coprime]
  exact (Nat.find_spec (exists_period d large coprime)).1

theorem first_spec (d : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d) :
    10 ^ first d % d = 1 := by
  rw [first_eq_find d large coprime]
  exact (Nat.find_spec (exists_period d large coprime)).2

theorem first_le (d : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d) : first d ≤ d := by
  rw [first_eq_find d large coprime]
  exact (Nat.find_min' (exists_period d large coprime)
    ⟨Nat.totient_pos.mpr (by omega), Nat.pow_totient_mod_eq_one large coprime⟩).trans
      (Nat.totient_le d)

theorem before_first (d k : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d)
    (positive : 0 < k) (before : k < first d) : 10 ^ k % d ≠ 1 := by
  rw [first_eq_find d large coprime] at before
  intro equal
  exact Nat.find_min (exists_period d large coprime) before ⟨positive, equal⟩

theorem next_remainder (d k : Nat) : (10 ^ k % d * 10) % d = 10 ^ (k + 1) % d := by
  simp [pow_succ, Nat.mul_mod]

private theorem scan_first (d k fuel : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d)
    (positive : 0 < k) (before : k ≤ first d) (enough : first d < k + fuel) :
    cycleLenAux.go d (10 ^ k % d) k fuel = first d := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
      rw [cycleLenAux.go]
      by_cases same : k = first d
      · subst k
        simp [first_spec d large coprime]
      · have smaller : k < first d := by omega
        rw [if_neg (before_first d k large coprime positive smaller), next_remainder]
        exact ih (k + 1) (by omega) (by omega) (by omega)

/-- The statement's bounded scan returns the same least period as the unbounded source loop. -/
theorem cycleLenAux_eq_first (d : Nat) (large : 1 < d) (coprime : Nat.Coprime 10 d) :
    cycleLenAux d = first d := by
  rw [cycleLenAux, if_neg (by omega : d ≠ 0)]
  have scanned := scan_first d 1 d large coprime (by decide)
    (first_pos d large coprime) (by have := first_le d large coprime; omega)
  simpa using scanned

end ProjectEulerStatements.RecurringCycle
