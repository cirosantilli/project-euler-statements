import ProjectEulerStatements.Lib.GaussianBinomial
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Int.Interval

/-! Signed columns and centered Gaussian rows retain their finite support and Pascal identities. -/
namespace ProjectEulerStatements.GaussianBinomial
variable {R : Type*} [Field R]
set_option Elab.async false

def column (q : R) (n : Nat) (k : Int) : R := if 0 ≤ k then choose q n k.toNat else 0

@[simp] theorem column_nat (q : R) (n k : Nat) : column q n k = choose q n k := by simp [column]

theorem column_negative (q : R) (n : Nat) (k : Int) (negative : k < 0) : column q n k = 0 := by
  simp [column, show ¬ 0 ≤ k by omega]

theorem column_above (q : R) (n : Nat) (k : Int) (above : (n : Int) < k) : column q n k = 0 := by
  rw [column, if_pos (by omega), choose_eq_zero q n k.toNat (by omega)]

theorem column_pascal (q : R) (n : Nat) (k : Int) :
    column q (n+1) k = column q n k + q^((n : Int)+1-k) * column q n (k-1) := by
  by_cases negative : k < 0
  · simp [column_negative q _ k negative, column_negative q n (k-1) (by omega)]
  · by_cases zero : k = 0
    · subst k
      simp [column]
    · by_cases above : (n : Int)+1 < k
      · rw [column_above q (n+1) k (by omega), column_above q n k (by omega),
          column_above q n (k-1) (by omega)]
        simp
      · lift k to Nat using (by omega : 0 ≤ k)
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        have difference : (n : Int)+1-(j+1 : Nat) = ((n-j : Nat) : Int) := by omega
        have previous : ((j+1 : Nat) : Int)-1 = (j : Int) := by omega
        rw [previous, difference]
        simp only [column_nat, zpow_natCast]
        exact choose_succ_succ q n j

theorem column_adjacent (q : R) (n : Nat) (k : Int) :
    (1-q^k) * column q n k = (1-q^((n : Int)+1-k)) * column q n (k-1) := by
  by_cases negative : k < 0
  · rw [column_negative q n k negative, column_negative q n (k-1) (by omega)]
    simp
  · by_cases zero : k = 0
    · subst k
      simp [column_negative q n (-1) (by omega)]
    · by_cases above : (n : Int)+1 < k
      · rw [column_above q n k (by omega), column_above q n (k-1) (by omega)]
        simp
      · lift k to Nat using (by omega : 0 ≤ k)
        have difference : (n : Int)+1-k = ((n+1-k : Nat) : Int) := by omega
        have previous : (k : Int)-1 = ((k-1 : Nat) : Int) := by omega
        rw [difference, previous]
        simp only [column_nat, zpow_natCast]
        exact adjacent q n k (by omega) (by omega)

theorem column_symm (q : R) (n : Nat) (k : Int) : column q n ((n : Int)-k) = column q n k := by
  by_cases negative : k < 0
  · rw [column_negative q n k negative, column_above q n ((n : Int)-k) (by omega)]
  · by_cases above : (n : Int) < k
    · rw [column_above q n k above, column_negative q n ((n : Int)-k) (by omega)]
    · lift k to Nat using (by omega : 0 ≤ k)
      have difference : (n : Int)-k = ((n-k : Nat) : Int) := by omega
      rw [difference, column_nat, column_nat]
      exact choose_symm q n k (by omega)

def row (q : R) (n : Nat) (k : Int) : R := column q (2*n) ((n : Int)+k)

theorem row_symmetric (q : R) (n : Nat) (k : Int) : row q n (-k) = row q n k := by
  have same := column_symm q (2*n) ((n : Int)+k)
  simpa only [row, Nat.cast_mul, Nat.cast_ofNat, show (2 : Int)*n-(n+k) = n+(-k) by ring] using same

theorem row_finite (q : R) (n : Nat) : Function.HasFiniteSupport (row q n) := by
  apply (Set.finite_Icc (-(n : Int)) n).subset
  intro k member
  by_contra outside
  have nonzero : row q n k ≠ 0 := member
  simp only [Set.mem_Icc, not_and_or, not_le] at outside
  rcases outside with below | above
  · exact nonzero (column_negative q (2*n) ((n : Int)+k) (by omega))
  · exact nonzero (column_above q (2*n) ((n : Int)+k) (by omega))

theorem row_adjacent (q : R) (n : Nat) (k : Int) :
    (1-q^((n : Int)+k)) * row q n k =
      (1-q^((n : Int)-k+1)) * row q n (k-1) := by
  have same := column_adjacent q (2*n) ((n : Int)+k)
  simpa only [row, Nat.cast_mul, Nat.cast_ofNat,
    show (2 : Int)*n+1-(n+k) = n-k+1 by ring,
    show (n : Int)+k-1 = n+(k-1) by ring] using same

theorem row_succ (q : R) (nonzero : q ≠ 0) (n : Nat) (k : Int) :
    row q (n+1) k = row q n (k+1) +
      (q^((n : Int)-k) + q^((n : Int)+1-k)) * row q n k +
      q^((2 : Int)*n+2-2*k) * row q n (k-1) := by
  have high : column q (2*n) (((n+1 : Nat) : Int)+k) = row q n (k+1) := by
    unfold row
    congr 1
    push_cast
    ring
  have center : column q (2*n) (((n+1 : Nat) : Int)+k-1) = row q n k := by
    unfold row
    congr 1
    push_cast
    ring
  have low : column q (2*n) ((((n+1 : Nat) : Int)+k-1)-1) = row q n (k-1) := by
    unfold row
    congr 1
    push_cast
    ring
  have outer : (((2*n+1 : Nat) : Int)+1)-(((n+1 : Nat) : Int)+k) = (n : Int)+1-k := by push_cast; ring
  have inner : (((2*n : Nat) : Int)+1)-(((n+1 : Nat) : Int)+k) = (n : Int)-k := by push_cast; ring
  have last : (((2*n : Nat) : Int)+1)-(((n+1 : Nat) : Int)+k-1) = (n : Int)+1-k := by push_cast; ring
  change column q (2*(n+1)) (((n+1 : Nat) : Int)+k) = _
  rw [show 2*(n+1) = 2*n+1+1 by omega, column_pascal, column_pascal, column_pascal,
    high, center, low, outer, inner, last]
  have powers : q^((2 : Int)*n+2-2*k) = q^((n : Int)+1-k) * q^((n : Int)+1-k) := by
    rw [← zpow_add₀ nonzero]
    congr 1
    ring
  rw [powers]
  ring

end ProjectEulerStatements.GaussianBinomial
