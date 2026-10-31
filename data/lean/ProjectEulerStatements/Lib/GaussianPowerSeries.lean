import ProjectEulerStatements.Lib.GaussianBinomial
import ProjectEulerStatements.Lib.PartitionGenerating

/-! Low coefficients of rectangular Gaussian polynomials count unrestricted partitions. -/
namespace ProjectEulerStatements.GaussianBinomial
open PartitionGenerating
open scoped BigOperators PowerSeries
set_option Elab.async false

theorem map_choose {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : R) (n k : Nat) : f (choose q n k) = choose (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose]
  | succ n ih => cases k <;> simp [choose, ih]

noncomputable section
variable {R : Type*} [CommRing R]

/-- Geometric factors of degrees greater than the requested coefficient cannot affect it. -/
theorem coeff_mul_high_product (f : R⟦X⟧) (n k d : Nat) (high : d+k ≤ n) :
    PowerSeries.coeff d (f * ∏ j ∈ Finset.range k, (1-PowerSeries.X^(n-j))) =
      PowerSeries.coeff d f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, mul_sub, mul_one, map_sub,
        PowerSeries.coeff_mul_X_pow', if_neg (by omega : ¬ n-k ≤ d), sub_zero]
      exact ih (by omega)

/-- Clearing denominators and using the bounded-part inverse gives the Gaussian series. -/
theorem choose_powerSeries (n k : Nat) (within : k ≤ n) :
    choose (PowerSeries.X : R⟦X⟧) n k =
      bounded k * ∏ j ∈ Finset.range k, (1-PowerSeries.X^(n-j)) := by
  have product := choose_mul_product (PowerSeries.X : R⟦X⟧) n k within
  change choose (PowerSeries.X : R⟦X⟧) n k * factors k = _ at product
  calc
    choose (PowerSeries.X : R⟦X⟧) n k =
        choose PowerSeries.X n k * (bounded k * factors k) := by rw [bounded_factors, mul_one]
    _ = bounded k * (choose PowerSeries.X n k * factors k) := by ring
    _ = bounded k * ∏ j ∈ Finset.range k, (1-PowerSeries.X^(n-j)) := by rw [product]

/-- A rectangle with both sides at least the degree contains every partition of that degree. -/
theorem coeff_choose_stable (n k d : Nat) (left : d ≤ k) (right : d+k ≤ n) :
    PowerSeries.coeff d (choose (PowerSeries.X : R⟦X⟧) n k) =
      (P76.countWays d d : R) := by
  rw [choose_powerSeries n k (by omega), coeff_mul_high_product _ n k d right,
    coeff_bounded_stable k d left]

end
end ProjectEulerStatements.GaussianBinomial
