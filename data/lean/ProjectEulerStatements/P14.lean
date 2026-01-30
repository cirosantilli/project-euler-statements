import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Iterate

namespace ProjectEulerStatements.P14

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Collatz conjecture: every starting value eventually reaches 1. -/
axiom collatzConjecture (n : Nat) : ∃ k, (collatzStep^[k]) n = 1

def collatzMeasure (n : Nat) : Nat :=
  Nat.find (collatzConjecture n)

lemma collatzMeasure_decreases {n : Nat} (h : n ≠ 1) :
    collatzMeasure (collatzStep n) < collatzMeasure n := by
  have hspec : (collatzStep^[collatzMeasure n]) n = 1 := by
    exact Nat.find_spec (collatzConjecture n)
  have hpos : 0 < collatzMeasure n := by
    by_contra h0
    have : collatzMeasure n = 0 := Nat.eq_zero_of_not_pos h0
    have hspec1 : n = 1 := by
      have hspec' := hspec
      simp [this] at hspec'
      simpa using hspec'
    exact h hspec1
  have hstep : (collatzStep^[collatzMeasure n - 1]) (collatzStep n) = 1 := by
    have hpred : (collatzMeasure n - 1).succ = collatzMeasure n := by
      simpa [Nat.pred_eq_sub_one] using (Nat.succ_pred_eq_of_pos hpos)
    have hspec' : (collatzStep^[ (collatzMeasure n - 1).succ]) n = 1 := by
      have hspec'' := hspec
      rw [← hpred] at hspec''
      exact hspec''
    simpa [Function.iterate_succ_apply] using hspec'
  have hle : collatzMeasure (collatzStep n) ≤ collatzMeasure n - 1 :=
    Nat.find_min' (collatzConjecture (collatzStep n)) hstep
  omega

/-- Length of a Collatz sequence starting at `n`. -/
def collatzLen (n : Nat) : Nat :=
  if h : n = 1 then
    1
  else
    1 + collatzLen (collatzStep n)
termination_by collatzMeasure n
decreasing_by
  exact collatzMeasure_decreases (n := n) h

/-- Which starting point under `limit` produces the longest Collatz sequence? -/
def naive (limit : Nat) : Nat :=
  match List.argmax (fun n => collatzLen n) (List.range (limit + 1)) with
  | some n => n
  | none => 0

example : collatzLen 13 = 10 := by
  native_decide

end ProjectEulerStatements.P14
