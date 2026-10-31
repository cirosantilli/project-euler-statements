import ProjectEulerStatements.Lib.GaussianPowerSeries
import ProjectEulerStatements.Lib.PentagonalFiniteProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.CharP.Algebra

/-! The finite pentagonal identity as a power-series identity, using an injective Laurent embedding. -/
namespace ProjectEulerStatements.PentagonalFinite
open GaussianBinomial
open scoped BigOperators PowerSeries LaurentSeries
set_option Elab.async false

noncomputable section

def sign (k : Int) : ℚ⟦X⟧ := if Even k then 1 else -1

theorem finite_powerSeries (n : Nat) :
    (∑ k ∈ Finset.Icc (-(n : Int)) n,
      sign k * PowerSeries.X^pentagonal k *
        choose PowerSeries.X (2*n) ((n : Int)+k).toNat) =
      ∏ j ∈ Finset.Ico (n+1) (2*n+1), (1-(PowerSeries.X : ℚ⟦X⟧)^j) := by
  let embed := HahnSeries.ofPowerSeries Int ℚ
  let q := embed PowerSeries.X
  letI : CharZero ℚ⸨X⸩ :=
    charZero_of_injective_ringHom (algebraMap ℚ ℚ⸨X⸩).injective
  have nonzero : q ≠ 0 := by
    intro zero
    have bad : (PowerSeries.X : ℚ⟦X⟧) = 0 :=
      HahnSeries.ofPowerSeries_injective (zero.trans (map_zero embed).symm)
    exact PowerSeries.X_ne_zero bad
  have finite := finite_pentagonal q nonzero n
  apply HahnSeries.ofPowerSeries_injective (Γ := Int)
  change embed _ = embed _
  rw [map_sum, map_prod]
  calc
    (∑ k ∈ Finset.Icc (-(n : Int)) n,
        embed (sign k * PowerSeries.X^pentagonal k *
          choose PowerSeries.X (2*n) ((n : Int)+k).toNat)) = moment q n 0 := by
      unfold moment
      apply Finset.sum_congr rfl
      intro k member
      have inside : 0 ≤ (n : Int)+k := by
        have lower := (Finset.mem_Icc.mp member).1
        omega
      simp only [map_mul, map_pow, map_choose, weight, zero_mul, add_zero,
        zpow_natCast, row, column, if_pos inside]
      simp only [sign, neg_one_zpow_eq_ite]
      split_ifs <;> simp only [map_one, map_neg] <;> rfl
    _ = intervalProduct q n := finite
    _ = ∏ j ∈ Finset.Ico (n+1) (2*n+1), embed (1-PowerSeries.X^j) := by
      simp only [map_sub, map_one, map_pow, intervalProduct]
      rfl

end
end ProjectEulerStatements.PentagonalFinite
