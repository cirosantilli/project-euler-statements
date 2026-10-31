import ProjectEulerStatements.Lib.PentagonalFinite
import Mathlib.Algebra.BigOperators.Intervals

/-! A finite pentagonal identity with no infinite-product convergence assumptions. -/
namespace ProjectEulerStatements.PentagonalFinite
open GaussianBinomial
open scoped BigOperators
variable {R : Type*} [Field R]
set_option Elab.async false

def intervalProduct (q : R) (n : Nat) : R :=
  ∏ j ∈ Finset.Ico (n+1) (2*n+1), (1-q^j)

theorem intervalProduct_succ (q : R) (n : Nat) :
    intervalProduct q (n+1) = (1+q^(n+1)) * (1-q^(2*n+1)) * intervalProduct q n := by
  by_cases zero : n = 0
  · subst n
    simp [intervalProduct]
    ring
  · have head : intervalProduct q n =
        (1-q^(n+1)) * ∏ j ∈ Finset.Ico (n+2) (2*n+1), (1-q^j) :=
      Finset.prod_eq_prod_Ico_succ_bot (by omega) _
    have tail : intervalProduct q (n+1) =
        ((∏ j ∈ Finset.Ico (n+2) (2*n+1), (1-q^j)) * (1-q^(2*n+1))) * (1-q^(2*n+2)) := by
      unfold intervalProduct
      rw [show n+1+1 = n+2 by omega, show 2*(n+1)+1 = (2*n+1)+1+1 by omega,
        Finset.prod_Ico_succ_top (by omega), Finset.prod_Ico_succ_top (by omega)]
    have twice : q^(2*n+2) = (q^(n+1))^2 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [tail, head, twice]
    ring

variable [CharZero R]

/-- The centered finite Gaussian sum equals the product over the upper half of the row. -/
theorem finite_pentagonal (q : R) (nonzero : q ≠ 0) (n : Nat) :
    moment q n 0 = intervalProduct q n := by
  induction n with
  | zero => simp [moment, weight, row, column, pentagonal, intervalProduct]
  | succ n ih =>
      rw [moment_succ q nonzero, ih, intervalProduct_succ]
      rw [show (n : Int)+1 = ((n+1 : Nat) : Int) by omega,
        show (2 : Int)*n+1 = ((2*n+1 : Nat) : Int) by omega]
      simp only [zpow_natCast]

end ProjectEulerStatements.PentagonalFinite
