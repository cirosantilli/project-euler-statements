import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P3

def isPrimeFactor (n k : Nat) : Prop :=
  2 ≤ k ∧ k ∣ n ∧ Nat.Prime k

instance (n k : Nat) : Decidable (isPrimeFactor n k) := by
  unfold isPrimeFactor
  infer_instance

instance (n : Nat) : DecidablePred (isPrimeFactor n) := by
  intro k
  infer_instance

def primeFactorSet (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun k => isPrimeFactor n k)

def naive (n : Nat) : Nat :=
  Nat.findGreatest (isPrimeFactor n) n

def naive2 (n : Nat) : Nat :=
  if h : (primeFactorSet n).Nonempty then
    (primeFactorSet n).max' h
  else
    0

theorem naive_eq_naive2 (n : Nat) : naive n = naive2 n := by
  classical
  by_cases hne : (primeFactorSet n).Nonempty
  · -- both are the maximal prime factor ≤ n
    have hm : isPrimeFactor n ((primeFactorSet n).max' hne) := by
      have hmem : (primeFactorSet n).max' hne ∈ primeFactorSet n := by
        exact Finset.max'_mem _ _
      have hmem' : (primeFactorSet n).max' hne ∈
          (Finset.range (n + 1)).filter (fun k => isPrimeFactor n k) := by
        simpa [primeFactorSet] using hmem
      simpa using (Finset.mem_filter.mp hmem').2
    have hm_le : (primeFactorSet n).max' hne ≤ n := by
      have hmem : (primeFactorSet n).max' hne ∈ primeFactorSet n := by
        exact Finset.max'_mem _ _
      have hmem' : (primeFactorSet n).max' hne ∈ Finset.range (n + 1) := by
        have hmem'' : (primeFactorSet n).max' hne ∈
            (Finset.range (n + 1)).filter (fun k => isPrimeFactor n k) := by
          simpa [primeFactorSet] using hmem
        exact (Finset.mem_filter.mp hmem'').1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hmem')
    have hmax :
        ∀ ⦃k⦄, (primeFactorSet n).max' hne < k → k ≤ n → ¬ isPrimeFactor n k := by
      intro k hk hk_le hPk
      have hk_mem : k ∈ primeFactorSet n := by
        have hk_mem' : k ∈ (Finset.range (n + 1)).filter (fun k => isPrimeFactor n k) := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
          · exact hPk
        simpa [primeFactorSet] using hk_mem'
      exact (not_lt_of_ge (Finset.le_max' _ _ hk_mem)) hk
    have hfg :
        Nat.findGreatest (isPrimeFactor n) n = (primeFactorSet n).max' hne := by
      apply (Nat.findGreatest_eq_iff (P := isPrimeFactor n) (k := n)
        (m := (primeFactorSet n).max' hne)).2
      refine ⟨hm_le, ?_, ?_⟩
      · intro hzero
        exact hm
      · intro k hk hk_le
        exact hmax hk hk_le
    simp [naive, naive2, hne, hfg]
  · -- no prime factors, both are 0
    have hzero :
        Nat.findGreatest (isPrimeFactor n) n = 0 := by
      apply (Nat.findGreatest_eq_zero_iff (P := isPrimeFactor n) (k := n)).2
      intro k hk_pos hk_le hkP
      have hk_mem : k ∈ primeFactorSet n := by
        have hk_mem' : k ∈ (Finset.range (n + 1)).filter (fun k => isPrimeFactor n k) := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
          · exact hkP
        simpa [primeFactorSet] using hk_mem'
      exact (hne (by exact ⟨k, hk_mem⟩))
    simp [naive, naive2, hne, hzero]

example : naive 13195 = 29 := by
  native_decide

end ProjectEulerStatements.P3
