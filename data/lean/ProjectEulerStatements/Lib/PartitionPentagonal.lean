import ProjectEulerStatements.Lib.PentagonalSeries

/-! Euler's signed pentagonal convolution for the bounded-part partition recurrence. -/
namespace ProjectEulerStatements.PartitionPentagonal
open GaussianBinomial PentagonalFinite
open scoped BigOperators PowerSeries
set_option Elab.async false

theorem index_bounds (k : Int) : -(pentagonal k : Int) ≤ k ∧ k ≤ (pentagonal k : Int) := by
  have quadratic := two_mul_natCast_pentagonal k
  by_cases positive : 0 < k
  · have product : 0 ≤ k*(k-1) := mul_nonneg (by omega) (by omega)
    constructor <;> nlinarith
  · by_cases zero : k = 0
    · subst k
      simp [pentagonal]
    · have product : 0 ≤ (-k)*(-k-1) := mul_nonneg (by omega) (by omega)
      constructor <;> nlinarith

noncomputable section

theorem coeff_mul_large_factors (f : ℚ⟦X⟧) (s : Finset Nat) (d : Nat)
    (high : ∀ j ∈ s, d < j) :
    PowerSeries.coeff d (f * ∏ j ∈ s, (1-PowerSeries.X^j)) = PowerSeries.coeff d f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s absent ih =>
      rw [Finset.prod_insert absent]
      have rearrange : f * ((1-PowerSeries.X^a) * ∏ j ∈ s, (1-PowerSeries.X^j)) =
          (f * ∏ j ∈ s, (1-PowerSeries.X^j)) * (1-PowerSeries.X^a) := by ring
      rw [rearrange, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow',
        if_neg (by have := high a (Finset.mem_insert_self a s); omega), sub_zero]
      exact ih (fun j member => high j (Finset.mem_insert_of_mem member))

theorem coeff_finite_product (n d : Nat) (large : d ≤ n) :
    PowerSeries.coeff d (∏ j ∈ Finset.Ico (n+1) (2*n+1),
      (1-(PowerSeries.X : ℚ⟦X⟧)^j)) = if d = 0 then 1 else 0 := by
  simpa only [one_mul, PowerSeries.coeff_one] using
    coeff_mul_large_factors 1 (Finset.Ico (n+1) (2*n+1)) d
      (fun j member => by have := (Finset.mem_Ico.mp member).1; omega)

def term (d : Nat) (k : Int) : ℚ :=
  if pentagonal k ≤ d then
    if Even k then (P76.countWays (d-pentagonal k) (d-pentagonal k) : ℚ)
    else -(P76.countWays (d-pentagonal k) (d-pentagonal k) : ℚ)
  else 0

theorem coeff_summand (d : Nat) (k : Int) :
    PowerSeries.coeff d (sign k * PowerSeries.X^pentagonal k *
      choose PowerSeries.X (4*d) (((2*d : Nat) : Int)+k).toNat) = term d k := by
  have rearrange : sign k * PowerSeries.X^pentagonal k *
      choose PowerSeries.X (4*d) (((2*d : Nat) : Int)+k).toNat =
      sign k * (PowerSeries.X^pentagonal k *
        choose PowerSeries.X (4*d) (((2*d : Nat) : Int)+k).toNat) := by ring
  rw [rearrange]
  by_cases inside : pentagonal k ≤ d
  · obtain ⟨lower, upper⟩ := index_bounds k
    have left : d-pentagonal k ≤ (((2*d : Nat) : Int)+k).toNat := by omega
    have right : d-pentagonal k + (((2*d : Nat) : Int)+k).toNat ≤ 4*d := by omega
    by_cases even : Even k
    · simp only [sign, if_pos even, one_mul, PowerSeries.coeff_X_pow_mul', if_pos inside]
      rw [coeff_choose_stable _ _ _ left right]
      simp only [term, if_pos inside, if_pos even]
    · simp only [sign, if_neg even, neg_one_mul, map_neg, PowerSeries.coeff_X_pow_mul',
        if_pos inside]
      rw [coeff_choose_stable _ _ _ left right]
      simp only [term, if_pos inside, if_neg even]
  · by_cases even : Even k <;>
      simp [sign, even, PowerSeries.coeff_X_pow_mul', inside, term]

/-- The coefficient at every positive degree vanishes; the constant coefficient is one. -/
theorem convolution (d : Nat) :
    (∑ k ∈ Finset.Icc (-((2*d : Nat) : Int)) (2*d), term d k) =
      if d = 0 then 1 else 0 := by
  have identity := congrArg (PowerSeries.coeff d) (finite_powerSeries (2*d))
  rw [map_sum, coeff_finite_product (2*d) d (by omega)] at identity
  convert identity using 1
  apply Finset.sum_congr rfl
  intro k member
  simpa only [show 2*(2*d) = 4*d by omega] using (coeff_summand d k).symm

end
end ProjectEulerStatements.PartitionPentagonal
