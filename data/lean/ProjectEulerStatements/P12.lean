import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace ProjectEulerStatements.P12

def triangle (n : Nat) : Nat :=
  n * (n + 1) / 2

def divisors (n : Nat) : Finset Nat :=
  Nat.divisors n

def divisorCount (n : Nat) : Nat :=
  (divisors n).card

theorem exists_triangle_divisorCount_gt (k : Nat) : ∃ n, divisorCount (triangle n) > k := by
  classical
  let p : Nat := 2
  have hp : Nat.Prime p := by decide
  have hdiv : divisorCount (p ^ k) = k + 1 := by
    simp [divisorCount, divisors, Nat.divisors_prime_pow hp, Finset.card_map]
  let a : Nat := p ^ k
  let n : Nat := 2 * a
  have htri : triangle n = a * (2 * a + 1) := by
    calc
      triangle n = (2 * a * (2 * a + 1)) / 2 := by
        simp [triangle, n]
      _ = (2 * (a * (2 * a + 1))) / 2 := by
        simp [Nat.mul_assoc]
      _ = a * (2 * a + 1) := by
        have h2 : 0 < 2 := Nat.succ_pos 1
        exact Nat.mul_div_right (a * (2 * a + 1)) h2
  have hpos : 0 < 2 * a + 1 := by
    exact Nat.succ_pos _
  have hsub : (Nat.divisors a) ⊆ Nat.divisors (a * (2 * a + 1)) := by
    intro d hd
    have hd' : d ∣ a := (Nat.mem_divisors.mp hd).1
    have ha0 : a ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hab0 : a * (2 * a + 1) ≠ 0 := by
      exact Nat.mul_ne_zero ha0 (ne_of_gt hpos)
    exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_left hd' _, hab0⟩
  have hcard : divisorCount a ≤ divisorCount (a * (2 * a + 1)) := by
    simpa [divisorCount, divisors] using (Finset.card_le_card hsub)
  have hgt : divisorCount (triangle n) > k := by
    have hcard' : divisorCount (triangle n) ≥ divisorCount a := by
      calc
        divisorCount (triangle n) = divisorCount (a * (2 * a + 1)) := by
          simp [htri]
        _ ≥ divisorCount a := hcard
    have : divisorCount a > k := by
      calc
        divisorCount a = k + 1 := by simpa [a] using hdiv
        _ > k := Nat.lt_succ_self k
    exact lt_of_lt_of_le this hcard'
  exact ⟨n, hgt⟩

noncomputable def firstTriangleOver (k : Nat) : Nat :=
  triangle (Nat.find (exists_triangle_divisorCount_gt k))

def naiveGo (k m n : Nat) (hm : divisorCount (triangle m) > k) (hn : n ≤ m) : Nat :=
  if h : divisorCount (triangle n) > k then
    triangle n
  else
    naiveGo k m (n + 1) hm (by
      have hne : n ≠ m := by
        intro hnm
        subst hnm
        exact (h hm).elim
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hn hne))
termination_by m - n
decreasing_by
  have hne : n ≠ m := by
    intro hnm
    subst hnm
    exact (h hm).elim
  have hlt : n < m := lt_of_le_of_ne hn hne
  omega

/-- First triangle number to have `k` divisors. -/
def naive (k : Nat) : Nat :=
  let m := Nat.find (exists_triangle_divisorCount_gt k)
  naiveGo k m 0 (Nat.find_spec (exists_triangle_divisorCount_gt k)) (Nat.zero_le _)

example : naive 5 = 28 := by
  native_decide

end ProjectEulerStatements.P12
