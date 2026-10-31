import ProjectEulerStatements.Lib.GaussianRows
import Mathlib.Combinatorics.Enumerative.Pentagonal
import Mathlib.Tactic.Linarith

/-! Finite weighted Gaussian sums for the pentagonal partition identity. -/
namespace ProjectEulerStatements.PentagonalFinite
open GaussianBinomial
open scoped BigOperators
variable {R : Type*} [Field R]
set_option Elab.async false

theorem pentagonal_neg_cast (k : Int) : (pentagonal (-k) : Int) = (pentagonal k : Int)+k := by
  have first := two_mul_natCast_pentagonal k
  have second := two_mul_natCast_pentagonal_neg k
  nlinarith

theorem pentagonal_succ_cast (k : Int) : (pentagonal (k+1) : Int) = (pentagonal k : Int)+3*k+1 := by
  have first := two_mul_natCast_pentagonal k
  have second := two_mul_natCast_pentagonal (k+1)
  nlinarith

def weight (q : R) (a k : Int) : R := (-1:R)^k * q^((pentagonal k : Int)+a*k)

theorem weight_neg (q : R) (a k : Int) : weight q a (-k) = weight q (1-a) k := by
  unfold weight
  rw [pentagonal_neg_cast]
  have sign : (-1:R)^(-k) = (-1:R)^k := by
    simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]
  rw [sign]
  congr 1
  congr 1
  ring

theorem weight_succ (q : R) (nonzero : q ≠ 0) (a k : Int) :
    weight q a (k+1) = -(q^(a+1) * weight q (a+3) k) := by
  unfold weight
  rw [pentagonal_succ_cast, zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_one]
  have exponent : (pentagonal k : Int)+3*k+1+a*(k+1) = (a+1)+((pentagonal k : Int)+(a+3)*k) := by ring
  rw [exponent, zpow_add₀ nonzero]
  ring

theorem weight_pred (q : R) (nonzero : q ≠ 0) (a k : Int) :
    weight q a (k-1) = -(q^(2-a) * weight q (a-3) k) := by
  have previous : (pentagonal (k-1) : Int) = (pentagonal k : Int)-3*k+2 := by
    have same := pentagonal_succ_cast (k-1)
    simp only [sub_add_cancel] at same
    omega
  unfold weight
  have sign : (-1:R)^(k-1) = -((-1:R)^k) := by
    rw [zpow_sub₀ (neg_ne_zero.mpr one_ne_zero), zpow_one]
    ring
  rw [previous, sign]
  have exponent : (pentagonal k : Int)-3*k+2+a*(k-1) = (2-a)+((pentagonal k : Int)+(a-3)*k) := by ring
  rw [exponent, zpow_add₀ nonzero]
  ring

theorem weight_scale (q : R) (nonzero : q ≠ 0) (a b k : Int) :
    q^(b*k) * weight q a k = weight q (a+b) k := by
  unfold weight
  rw [mul_left_comm, ← zpow_add₀ nonzero]
  congr 1
  congr 1
  ring

def moment (q : R) (n : Nat) (a : Int) : R :=
  ∑ k ∈ Finset.Icc (-(n : Int)) n, weight q a k * row q n k

theorem moment_finsum (q : R) (n : Nat) (a : Int) :
    moment q n a = ∑ᶠ k : Int, weight q a k * row q n k := by
  symm
  apply finsum_eq_sum_of_support_subset
  intro k member
  have live : row q n k ≠ 0 := (mul_ne_zero_iff.mp member).2
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · by_contra before
    exact live (column_negative q (2*n) ((n : Int)+k) (by omega))
  · by_contra after
    exact live (column_above q (2*n) ((n : Int)+k) (by omega))

theorem weighted_finite (q : R) (n : Nat) (a : Int) :
    Function.HasFiniteSupport (fun k => weight q a k * row q n k) :=
  Function.HasFiniteSupport.mul_right _ (row_finite q n)

theorem moment_reflect (q : R) (n : Nat) (a : Int) : moment q n a = moment q n (1-a) := by
  rw [moment_finsum, moment_finsum, ← finsum_comp_equiv (Equiv.neg Int)]
  apply finsum_congr
  intro k
  simp only [Equiv.neg_apply, weight_neg, row_symmetric]

theorem weight_affine (q : R) (nonzero : q ≠ 0) (a b c k : Int) :
    q^(c+b*k) * weight q a k = q^c * weight q (a+b) k := by
  rw [zpow_add₀ nonzero, mul_assoc, weight_scale q nonzero]

private theorem finsum_linear (f g : Int → R) (hf : Function.HasFiniteSupport f)
    (hg : Function.HasFiniteSupport g) (c d : R) :
    (∑ᶠ k, (c*f k+d*g k)) = c*(∑ᶠ k, f k)+d*(∑ᶠ k, g k) := by
  have left : Function.HasFiniteSupport (fun k => c*f k) :=
    Function.HasFiniteSupport.mul_right (fun _ => c) hf
  have right : Function.HasFiniteSupport (fun k => d*g k) :=
    Function.HasFiniteSupport.mul_right (fun _ => d) hg
  rw [finsum_add_distrib left right, ← mul_finsum, ← mul_finsum]

theorem moment_shift_pred (q : R) (nonzero : q ≠ 0) (n : Nat) (a : Int) :
    (∑ᶠ k, weight q a k * row q n (k-1)) = -(q^(a+1) * moment q n (a+3)) := by
  calc
    (∑ᶠ k, weight q a k * row q n (k-1)) =
        ∑ᶠ k, weight q a (k+1) * row q n ((k+1)-1) :=
      (finsum_comp_equiv (Equiv.addRight (1 : Int))).symm
    _ = ∑ᶠ k, (-q^(a+1)) * (weight q (a+3) k * row q n k) := by
      apply finsum_congr
      intro k
      rw [add_sub_cancel_right, weight_succ q nonzero]
      ring
    _ = -(q^(a+1) * moment q n (a+3)) := by
      rw [← mul_finsum, ← moment_finsum]
      ring

theorem moment_shift_succ (q : R) (nonzero : q ≠ 0) (n : Nat) (a : Int) :
    (∑ᶠ k, weight q a k * row q n (k+1)) = -(q^(2-a) * moment q n (a-3)) := by
  calc
    (∑ᶠ k, weight q a k * row q n (k+1)) =
        ∑ᶠ k, weight q a (k-1) * row q n ((k-1)+1) :=
      (finsum_comp_equiv (Equiv.addRight (-1 : Int))).symm
    _ = ∑ᶠ k, (-q^(2-a)) * (weight q (a-3) k * row q n k) := by
      apply finsum_congr
      intro k
      rw [sub_add_cancel, weight_pred q nonzero]
      ring
    _ = -(q^(2-a) * moment q n (a-3)) := by
      rw [← mul_finsum, ← moment_finsum]
      ring

/-- The Gaussian adjacent-column equation becomes a four-moment identity. -/
theorem moment_adjacent (q : R) (nonzero : q ≠ 0) (n : Nat) (a : Int) :
    moment q n a + q^(a+1) * moment q n (a+3) =
      q^(n : Int) * moment q n (a+1) + q^((n : Int)+a+1) * moment q n (a+2) := by
  have shifted_finite (b : Int) :
      Function.HasFiniteSupport (fun k => weight q b k * row q n (k-1)) :=
    Function.HasFiniteSupport.mul_right _
      (Function.HasFiniteSupport.comp_of_injective (f := row q n) (g := fun k : Int => k-1)
        (fun x y same => by change x-1 = y-1 at same; omega) (row_finite q n))
  have pointwise (k : Int) :
      weight q a k * row q n k - q^(n : Int) * (weight q (a+1) k * row q n k) =
        weight q a k * row q n (k-1) - q^((n : Int)+1) * (weight q (a-1) k * row q n (k-1)) := by
    have leftScale : q^((n : Int)+k) * weight q a k = q^(n : Int) * weight q (a+1) k := by
      simpa only [one_mul] using weight_affine q nonzero a 1 n k
    have rightScale : q^((n : Int)-k+1) * weight q a k = q^((n : Int)+1) * weight q (a-1) k := by
      rw [show (n : Int)-k+1 = (n : Int)+1+(-1)*k by ring, show a-1 = a+(-1) by ring]
      exact weight_affine q nonzero a (-1) ((n : Int)+1) k
    calc
      weight q a k * row q n k - q^(n : Int) * (weight q (a+1) k * row q n k) =
          weight q a k * ((1-q^((n : Int)+k)) * row q n k) := by
        linear_combination (row q n k)*leftScale
      _ = weight q a k * ((1-q^((n : Int)-k+1)) * row q n (k-1)) := by rw [row_adjacent]
      _ = weight q a k * row q n (k-1) - q^((n : Int)+1) * (weight q (a-1) k * row q n (k-1)) := by
        linear_combination -(row q n (k-1))*rightScale
  have leftSum :
      (∑ᶠ k, (weight q a k * row q n k - q^(n : Int) * (weight q (a+1) k * row q n k))) =
        moment q n a - q^(n : Int) * moment q n (a+1) := by
    simpa only [one_mul, neg_mul, sub_eq_add_neg, moment_finsum] using
      finsum_linear _ _ (weighted_finite q n a) (weighted_finite q n (a+1)) 1 (-q^(n : Int))
  have rightSum :
      (∑ᶠ k, (weight q a k * row q n (k-1) - q^((n : Int)+1) * (weight q (a-1) k * row q n (k-1)))) =
        (∑ᶠ k, weight q a k * row q n (k-1)) -
          q^((n : Int)+1) * (∑ᶠ k, weight q (a-1) k * row q n (k-1)) := by
    simpa only [one_mul, neg_mul, sub_eq_add_neg] using
      finsum_linear _ _ (shifted_finite a) (shifted_finite (a-1)) 1 (-q^((n : Int)+1))
  have summed := finsum_congr pointwise
  rw [leftSum, rightSum, moment_shift_pred q nonzero, moment_shift_pred q nonzero] at summed
  simp only [sub_add_cancel, show a-1+3 = a+2 by ring] at summed
  have powers : q^((n : Int)+a+1) = q^((n : Int)+1) * q^a := by
    rw [← zpow_add₀ nonzero]
    congr 1
    ring
  rw [powers]
  linear_combination summed

private theorem weighted_shift_finite (q : R) (n : Nat) (a b : Int) :
    Function.HasFiniteSupport (fun k => weight q a k * row q n (k+b)) :=
  Function.HasFiniteSupport.mul_right _
    (Function.HasFiniteSupport.comp_of_injective (f := row q n) (g := fun k : Int => k+b)
      (fun x y same => by change x+b = y+b at same; exact add_right_cancel same) (row_finite q n))

private theorem finsum_three (f g h : Int → R)
    (hf : Function.HasFiniteSupport f) (hg : Function.HasFiniteSupport g)
    (hh : Function.HasFiniteSupport h) (c d : R) :
    (∑ᶠ k, (f k+c*g k+d*h k)) = (∑ᶠ k, f k)+c*(∑ᶠ k, g k)+d*(∑ᶠ k, h k) := by
  have cg : Function.HasFiniteSupport (fun k => c*g k) := Function.HasFiniteSupport.mul_right _ hg
  have dh : Function.HasFiniteSupport (fun k => d*h k) := Function.HasFiniteSupport.mul_right _ hh
  have fg : Function.HasFiniteSupport (fun k => f k+c*g k) := hf.add cg
  rw [finsum_add_distrib fg dh, finsum_add_distrib hf cg, ← mul_finsum, ← mul_finsum]

/-- Two Pascal steps reduce the next central moment to three moments of the preceding row. -/
theorem moment_succ_expand (q : R) (nonzero : q ≠ 0) (n : Nat) :
    moment q (n+1) 0 = -(q^(2 : Int) * moment q n (-3)) +
      (q^(n : Int)+q^((n : Int)+1)) * moment q n (-1) -
      q^((2 : Int)*n+1) * moment q n 1 := by
  have pointwise (k : Int) :
      weight q 0 k * row q (n+1) k = weight q 0 k * row q n (k+1) +
        (q^(n : Int)+q^((n : Int)+1)) * (weight q (-1) k * row q n k) +
        q^((2 : Int)*n+2) * (weight q (-2) k * row q n (k-1)) := by
    have first : q^((n : Int)-k) * weight q 0 k = q^(n : Int) * weight q (-1) k := by
      simpa only [zero_add, neg_one_mul, sub_eq_add_neg] using weight_affine q nonzero 0 (-1) n k
    have second : q^((n : Int)+1-k) * weight q 0 k = q^((n : Int)+1) * weight q (-1) k := by
      simpa only [zero_add, neg_one_mul, sub_eq_add_neg] using weight_affine q nonzero 0 (-1) ((n : Int)+1) k
    have third : q^((2 : Int)*n+2-2*k) * weight q 0 k = q^((2 : Int)*n+2) * weight q (-2) k := by
      simpa only [zero_add, neg_mul, sub_eq_add_neg] using weight_affine q nonzero 0 (-2) ((2 : Int)*n+2) k
    rw [row_succ q nonzero]
    linear_combination (row q n k)*first + (row q n k)*second + (row q n (k-1))*third
  have shifted : Function.HasFiniteSupport (fun k => weight q (-2) k * row q n (k-1)) := by
    simpa only [sub_eq_add_neg] using weighted_shift_finite q n (-2) (-1)
  have expanded := finsum_congr pointwise
  rw [← moment_finsum, finsum_three _ _ _ (weighted_shift_finite q n 0 1)
    (weighted_finite q n (-1)) shifted, moment_shift_succ q nonzero,
    ← moment_finsum, moment_shift_pred q nonzero] at expanded
  have powers : q^((2 : Int)*n+2) * q^(-1 : Int) = q^((2 : Int)*n+1) := by
    rw [← zpow_add₀ nonzero]
    congr 1
    ring
  simpa only [sub_zero, zero_sub, neg_add_cancel, Int.reduceNeg, Int.reduceAdd,
    mul_neg, ← mul_assoc, powers, sub_eq_add_neg] using expanded

variable [CharZero R]

/-- The two reflected moments in the adjacent identity coincide. -/
theorem moment_minus_one (q : R) (nonzero : q ≠ 0) (n : Nat) :
    moment q n (-1) = q^(n : Int) * moment q n 0 := by
  have relation := moment_adjacent q nonzero n (-1)
  have reflected := moment_reflect q n (-1)
  have central := moment_reflect q n 0
  norm_num only [Int.reduceNeg, Int.reduceAdd, zpow_zero, one_mul] at relation reflected central
  rw [← reflected, ← central] at relation
  rw [show (n : Int)+(-1)+1 = (n : Int) by ring] at relation
  have two : (2 : R) ≠ 0 := by exact_mod_cast (by decide : (2 : Int) ≠ 0)
  apply (mul_left_cancel₀ two)
  linear_combination relation

/-- Central weighted Gaussian sums obey a first-order finite pentagonal recurrence. -/
theorem moment_succ (q : R) (nonzero : q ≠ 0) (n : Nat) :
    moment q (n+1) 0 =
      (1+q^((n : Int)+1)) * (1-q^((2 : Int)*n+1)) * moment q n 0 := by
  have first := moment_adjacent q nonzero n 0
  have third := moment_adjacent q nonzero n (-3)
  have reflected := moment_reflect q n (-2)
  have upper := moment_reflect q n (-1)
  have central := moment_reflect q n 0
  have previous := moment_minus_one q nonzero n
  have expanded := moment_succ_expand q nonzero n
  norm_num only [zero_add, add_zero, Int.reduceNeg, Int.reduceAdd] at first third reflected central upper
  rw [← central] at first expanded
  rw [← upper, previous] at first
  rw [previous] at expanded third
  rw [reflected] at third
  have square : q^((2 : Int)*n+1) = q^(n : Int)*q^(n : Int)*q := by
    calc
      q^((2 : Int)*n+1) = q^((n : Int)+n+1) := by congr 1; ring
      _ = q^((n : Int)+n)*q := by rw [zpow_add₀ nonzero, zpow_one]
      _ = q^(n : Int)*q^(n : Int)*q := by rw [zpow_add₀ nonzero]
  have next : q^((n : Int)+1) = q^(n : Int)*q := by rw [zpow_add₀ nonzero, zpow_one]
  have back : q^((n : Int)+(-3)+1) = q^((n : Int)-2) := by congr 1; ring
  have cancel : q^(2 : Int)*q^(-2 : Int) = (1 : R) := by rw [← zpow_add₀ nonzero]; norm_num
  have shifted : q^(2 : Int)*q^((n : Int)-2) = q^(n : Int) := by
    rw [← zpow_add₀ nonzero]
    congr 1
    ring
  rw [back] at third
  simp only [square, next, zpow_one] at first expanded ⊢
  have scaled := congrArg (fun value : R => q^(2 : Int)*value) third
  simp only [mul_add, ← mul_assoc, cancel, shifted] at scaled
  simp only [zpow_natCast, zpow_two] at first expanded scaled ⊢
  linear_combination expanded - scaled - q^n*q*first

end ProjectEulerStatements.PentagonalFinite
