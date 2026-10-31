import ProjectEulerStatements.Lib.CoinChange
import Mathlib.Data.List.Range

/-! Unordered partitions using positive parts smaller than the supplied integer. -/
namespace ProjectEulerStatements.P76
set_option Elab.async false

def countWays (n max : Nat) : Nat :=
  if n = 0 then 1
  else if max = 0 then 0
  else (if max ≤ n then countWays (n-max) max else 0) + countWays n (max-1)
termination_by n+max
decreasing_by all_goals omega

@[simp] theorem countWays_zero (max : Nat) : countWays 0 max = 1 := by
  rw [countWays, if_pos rfl]

@[simp] theorem countWays_no_parts (n : Nat) : countWays n 0 = if n = 0 then 1 else 0 := by
  rw [countWays]
  split <;> simp_all

theorem countWays_step (n max : Nat) (nonzero : n ≠ 0) (positive : 0 < max) :
    countWays n max = (if max ≤ n then countWays (n-max) max else 0) + countWays n (max-1) := by
  rw [countWays, if_neg nonzero, if_neg (by omega)]

/-- The descending denomination list contains every permitted positive part exactly once. -/
theorem countWays_coins (n max : Nat) :
    countWays n max = P31.countWaysBound n (List.range' 1 max).reverse := by
  induction measure : n+max using Nat.strong_induction_on generalizing n max with
  | h size ih =>
      by_cases empty : n = 0
      · subst n
        simp
      · cases max with
        | zero => simp [empty]
        | succ max =>
            have split : (List.range' 1 (max+1)).reverse =
                (max+1) :: (List.range' 1 max).reverse := by
              rw [List.range'_concat, List.reverse_append]
              simp [Nat.add_comm]
            rw [split, countWays_step n (max+1) empty (by omega),
              CoinChange.countWaysBound_cons n (max+1) _ (by omega)]
            have fewer := ih (n+max) (by omega) n max rfl
            simp only [Nat.add_sub_cancel]
            rw [fewer]
            by_cases enough : max+1 ≤ n
            · rw [if_pos enough, if_pos enough,
                ih ((n-(max+1))+(max+1)) (by omega) (n-(max+1)) (max+1) rfl, split]
              omega
            · rw [if_neg enough, if_neg enough]
              omega

def countPartitions (n : Nat) : Nat := countWays n (n-1)

def bounded (n max : Int) : Int := if n < 0 then 0 else countWays n.toNat max.toNat

theorem bounded_nat (n max : Nat) : bounded n max = (countWays n max : Int) := by
  simp [bounded]


@[simp] theorem bounded_zero (max : Int) : bounded 0 max = 1 := by simp [bounded]

theorem bounded_negative (n max : Int) (negative : n < 0) : bounded n max = 0 := by
  simp [bounded, negative]

theorem bounded_no_parts (n max : Int) (positive : 0 < n) (nonpositive : max ≤ 0) :
    bounded n max = 0 := by
  have empty : max.toNat = 0 := by omega
  have nonzero : n.toNat ≠ 0 := by omega
  simp [bounded, show ¬ n < 0 by omega, empty, nonzero]

theorem bounded_step (n max : Int) (nPositive : 0 < n) (maxPositive : 0 < max) :
    bounded n max = (if max ≤ n then bounded (n-max) max else 0) + bounded n (max-1) := by
  lift n to Nat using (by omega : 0 ≤ n)
  lift max to Nat using (by omega : 0 ≤ max)
  have decrement : (max : Int)-1 = ((max-1 : Nat) : Int) := by omega
  rw [decrement, bounded_nat, bounded_nat, countWays_step _ _ (by omega) (by omega)]
  by_cases enough : max ≤ n
  · have difference : (n : Int)-max = ((n-max : Nat) : Int) := by omega
    simp only [Int.ofNat_le, if_pos enough, difference, bounded_nat, Int.natCast_add]
  · simp only [Int.ofNat_le, if_neg enough, Nat.zero_add, Int.zero_add]

def result (n : Int) : Int := bounded n (n-1)


def naive (n : Int) : Int := result n

theorem result_nat (n : Nat) : result n = (countPartitions n : Int) := by
  simp [result, bounded, countPartitions]

theorem result_negative (n : Int) (negative : n < 0) : result n = 0 := by
  simp [result, bounded, negative]

end ProjectEulerStatements.P76
