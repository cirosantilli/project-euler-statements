import Mathlib.Data.Nat.Totient
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

/-! Counting reduced proper fractions by denominator, excluding denominators zero and one. -/
namespace ProjectEulerStatements.ReducedFractionCount
set_option Elab.async false

/-- Count the residues below d that are coprime to d, including the residue zero for d = 1. -/
def countReduced (d : Nat) : Nat :=
  ((Finset.range d).filter (fun n => Nat.gcd n d = 1)).card

theorem countReduced_eq_totient (d : Nat) : countReduced d = d.totient := by
  simpa [countReduced, Nat.Coprime, Nat.gcd_comm] using (Nat.totient_eq_card_coprime d).symm

def contribution (d : Nat) : Nat := if 1 < d then d.totient else 0

def result (limit : Int) : Nat :=
  ((List.range (limit + 1).toNat).map contribution).sum

theorem result_small (limit : Int) (small : limit < 2) : result limit = 0 := by
  have bound : (limit + 1).toNat ≤ 2 := by omega
  interval_cases h : (limit + 1).toNat <;> simp [result, h, contribution, List.range_succ]

/-- Removing the first two table entries is exactly the denominator filter in the reference. -/
theorem tail_sum (size : Nat) :
    (((List.range size).drop 2).map Nat.totient).sum =
      ((List.range size).map contribution).sum := by
  cases size with
  | zero => rfl
  | succ size =>
      cases size with
      | zero => rfl
      | succ size =>
          have same : (List.range' 2 size).map contribution =
              (List.range' 2 size).map Nat.totient := by
            apply List.map_congr_left
            intro d member
            obtain ⟨i, _, value⟩ := List.mem_range'.mp member
            exact if_pos (by omega)
          simpa only [List.range_eq_range', List.range'_succ, Nat.zero_add,
            List.drop_succ_cons, List.drop_zero, List.map_cons, List.sum_cons,
            contribution, show ¬ 1 < 0 from by omega, show ¬ 1 < 1 from by omega,
            if_false, Nat.zero_add] using congrArg List.sum same.symm

end ProjectEulerStatements.ReducedFractionCount
