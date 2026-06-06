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

def NatGE2 := {n : Nat // 2 ≤ n}

def primeFactorSet (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun k => isPrimeFactor n k)

def naive (n : NatGE2) : Nat :=
  Nat.findGreatest (isPrimeFactor n.1) n.1

lemma primeFactorSet_nonempty (n : NatGE2) :
    (primeFactorSet n.1).Nonempty := by
  have hn : 2 ≤ n.1 := n.property
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hn))
  have hp2 : 2 ≤ p := hp.two_le
  have hnpos : 0 < n.1 := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hp_le : p ≤ n.1 := Nat.le_of_dvd hnpos hpdvd
  refine ⟨p, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hp_le)
  · exact ⟨hp2, hpdvd, hp⟩

def naive2 (n : NatGE2) : Nat :=
  (primeFactorSet n.1).max' (primeFactorSet_nonempty n)

theorem naive_eq_naive2 (n : NatGE2) : naive n = naive2 n := by
  classical
  -- both are the maximal prime factor ≤ n
  have hne : (primeFactorSet n.1).Nonempty :=
    primeFactorSet_nonempty n
  have hm : isPrimeFactor n.1 ((primeFactorSet n.1).max' hne) := by
    have hmem : (primeFactorSet n.1).max' hne ∈ primeFactorSet n.1 := by
      exact Finset.max'_mem _ _
    have hmem' : (primeFactorSet n.1).max' hne ∈
        (Finset.range (n.1 + 1)).filter (fun k => isPrimeFactor n.1 k) := by
      simpa [primeFactorSet] using hmem
    simpa using (Finset.mem_filter.mp hmem').2
  have hm_le : (primeFactorSet n.1).max' hne ≤ n.1 := by
    have hmem : (primeFactorSet n.1).max' hne ∈ primeFactorSet n.1 := by
      exact Finset.max'_mem _ _
    have hmem' : (primeFactorSet n.1).max' hne ∈ Finset.range (n.1 + 1) := by
      have hmem'' : (primeFactorSet n.1).max' hne ∈
          (Finset.range (n.1 + 1)).filter (fun k => isPrimeFactor n.1 k) := by
        simpa [primeFactorSet] using hmem
      exact (Finset.mem_filter.mp hmem'').1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hmem')
  have hmax :
      ∀ ⦃k⦄, (primeFactorSet n.1).max' hne < k → k ≤ n.1 → ¬ isPrimeFactor n.1 k := by
    intro k hk hk_le hPk
    have hk_mem : k ∈ primeFactorSet n.1 := by
      have hk_mem' : k ∈ (Finset.range (n.1 + 1)).filter (fun k => isPrimeFactor n.1 k) := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
        · exact hPk
      simpa [primeFactorSet] using hk_mem'
    exact (not_lt_of_ge (Finset.le_max' _ _ hk_mem)) hk
  have hfg :
      Nat.findGreatest (isPrimeFactor n.1) n.1 = (primeFactorSet n.1).max' hne := by
    apply (Nat.findGreatest_eq_iff (P := isPrimeFactor n.1) (k := n.1)
      (m := (primeFactorSet n.1).max' hne)).2
    refine ⟨hm_le, ?_, ?_⟩
    · intro hzero
      exact hm
    · intro k hk hk_le
      exact hmax hk hk_le
  simp [naive, naive2, hfg]

example : naive ⟨13195, by decide⟩ = 29 := by
  native_decide

end ProjectEulerStatements.P3
