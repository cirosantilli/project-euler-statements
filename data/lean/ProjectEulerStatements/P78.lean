import ProjectEulerStatements.Lib.PartitionSearch
import ProjectEulerStatements.Lib.UnboundedSearch

/-! An unbounded exact-partition search; the least partial result records divergence by bottom. -/
namespace ProjectEulerStatements.P78
open UnboundedSearch PartitionSearch
set_option Elab.async false

def partition (n : Nat) : Nat := P76.countWays n n

def step (modulus : Int) (n : Nat) : Sum Nat Nat :=
  if (partition n : Int) % modulus = 0 then .inl n else .inr (n+1)

def search (modulus : Int) (n : Nat) : Option Nat := run (step modulus) n

def naive (modulus : Int) : Option Nat := search modulus 1

theorem search_spec (modulus : Int) (n result : Nat) (returned : search modulus n = some result) :
    n ≤ result ∧ (partition result : Int) % modulus = 0 := by
  have finished := (run_some_iff (step modulus) n result).mp returned
  clear returned
  induction finished with
  | @done n result transition =>
      simp only [step] at transition
      split at transition
      · cases transition
        exact ⟨le_refl _, by assumption⟩
      · contradiction
  | @next n next result transition rest ih =>
      simp only [step] at transition
      split at transition
      · contradiction
      · cases transition
        exact ⟨by omega, ih.2⟩

theorem search_result (modulus : Int) (success : Success modulus) (n : Nat)
    (positive : 0 < n) (upper : n ≤ answer modulus success) :
    search modulus n = some (answer modulus success) := by
  rw [search, run.eq_1]
  simp only [step]
  by_cases same : n = answer modulus success
  · have divides : (partition n : Int) % modulus = 0 := by
      simpa only [same, partition] using (answer_spec modulus success).2
    rw [if_pos divides, same]
  · have earlier : n < answer modulus success := by omega
    have missing : (partition n : Int) % modulus ≠ 0 :=
      before_answer modulus success n positive earlier
    rw [if_neg missing]
    exact search_result modulus success (n+1) (by omega) (by omega)
termination_by answer modulus success-n
decreasing_by omega

theorem naive_result (modulus : Int) (success : Success modulus) :
    naive modulus = some (answer modulus success) :=
  search_result modulus success 1 (by omega) (answer_positive modulus success)

theorem naive_none (modulus : Int) (missing : ¬ Success modulus) : naive modulus = none := by
  cases returned : naive modulus with
  | none => rfl
  | some result =>
      have spec := search_spec modulus 1 result returned
      exact False.elim (missing ⟨result, by omega, spec.2⟩)

end ProjectEulerStatements.P78
