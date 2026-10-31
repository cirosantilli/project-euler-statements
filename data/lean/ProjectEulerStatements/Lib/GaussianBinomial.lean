import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Gaussian coefficients and their adjacent-column identities over an arbitrary commutative ring. -/
namespace ProjectEulerStatements.GaussianBinomial
open scoped BigOperators
variable {R : Type*} [CommRing R]
set_option Elab.async false

def choose (q : R) : Nat → Nat → R
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => choose q n (k+1) + q^(n-k) * choose q n k

@[simp] theorem choose_zero (q : R) (n : Nat) : choose q n 0 = 1 := by
  cases n <;> rfl

theorem choose_succ_succ (q : R) (n k : Nat) :
    choose q (n+1) (k+1) = choose q n (k+1) + q^(n-k) * choose q n k := rfl

theorem choose_eq_zero (q : R) (n k : Nat) (outside : n < k) : choose q n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k => rw [choose_succ_succ, ih (k+1) (by omega), ih k (by omega)]; simp

@[simp] theorem choose_self (q : R) (n : Nat) : choose q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose_succ_succ, choose_eq_zero q n (n+1) (by omega), ih]; simp

/-- Multiplying adjacent columns removes their geometric denominator. -/
theorem adjacent (q : R) (n k : Nat) (positive : 0 < k) (within : k ≤ n+1) :
    (1-q^k) * choose q n k = (1-q^(n+1-k)) * choose q n (k-1) := by
  induction n generalizing k with
  | zero =>
      have same : k = 1 := by omega
      subst k
      simp [choose]
  | succ n ih =>
      by_cases top : k = n+2
      · subst k
        rw [choose_eq_zero q (n+1) (n+2) (by omega)]
        simp
      · have inside : k ≤ n+1 := by omega
        cases k with
        | zero => omega
        | succ k =>
            cases k with
            | zero =>
                have previous : (1-q) * choose q n 1 = 1-q^n := by
                  simpa using ih 1 (by omega) (by omega)
                rw [choose_succ_succ]
                simpa using calc
                    (1-q) * (choose q n 1 + q^n) =
                        (1-q) * choose q n 1 + (1-q) * q^n := by ring
                    _ = (1-q^n) + (1-q) * q^n := by rw [previous]
                    _ = 1-q^(n+1) := by rw [pow_succ]; ring
            | succ k =>
                have first := ih (k+2) (by omega) inside
                have second := ih (k+1) (by omega) (by omega)
                have e1 : n+1-(k+2) = n-(k+1) := by omega
                have e2 : n+1-(k+1) = n-k := by omega
                have step : n-k = (n-(k+1))+1 := by omega
                simp only [show k+2-1 = k+1 by omega, e1] at first
                simp only [Nat.add_sub_cancel, e2] at second
                simp only [show k+1+1-1 = k+1 by omega, show n+1+1-(k+1+1) = n-k by omega]
                change (1-q^(k+2)) * choose q (n+1) (k+2) =
                  (1-q^(n-k)) * choose q (n+1) (k+1)
                rw [choose_succ_succ, choose_succ_succ, step]
                rw [step] at second
                simp only [pow_succ] at first second ⊢
                linear_combination first + q^(n-(k+1))*q*second

/-- The alternate Pascal identity is valid at both boundary columns as well. -/
theorem choose_succ (q : R) (n k : Nat) :
    choose q (n+1) (k+1) = q^(k+1) * choose q n (k+1) + choose q n k := by
  by_cases within : k+1 ≤ n+1
  · have relation := adjacent q n (k+1) (by omega) within
    simp only [Nat.add_sub_cancel, show n+1-(k+1) = n-k by omega] at relation
    rw [choose_succ_succ]
    linear_combination relation
  · rw [choose_eq_zero q (n+1) (k+1) (by omega),
      choose_eq_zero q n (k+1) (by omega), choose_eq_zero q n k (by omega)]
    simp

/-- Gaussian rows are symmetric around their middle column. -/
theorem choose_symm (q : R) (n k : Nat) (within : k ≤ n) : choose q n (n-k) = choose q n k := by
  induction n generalizing k with
  | zero =>
      have same : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases zero : k = 0
      · subst k; simp
      · by_cases top : k = n+1
        · subst k; simp
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero zero
          have bounded : j+1 ≤ n := by omega
          have reflect : n+1-(j+1) = (n-(j+1))+1 := by omega
          rw [reflect, choose_succ_succ, show n-(j+1)+1 = n-j by omega,
            ih j (by omega), ih (j+1) bounded,
            show n-(n-(j+1)) = j+1 by omega]
          rw [choose_succ]
          ring

/-- Clearing the finite geometric factors gives the rectangular partition product. -/
theorem choose_mul_product (q : R) (n k : Nat) (within : k ≤ n) :
    choose q n k * ∏ j ∈ Finset.range k, (1-q^(j+1)) =
      ∏ j ∈ Finset.range k, (1-q^(n-j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have relation := adjacent q n (k+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel, show n+1-(k+1) = n-k by omega] at relation
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        choose q n (k+1) * ((∏ j ∈ Finset.range k, (1-q^(j+1))) * (1-q^(k+1))) =
            ((1-q^(k+1)) * choose q n (k+1)) * ∏ j ∈ Finset.range k, (1-q^(j+1)) := by ring
        _ = ((1-q^(n-k)) * choose q n k) * ∏ j ∈ Finset.range k, (1-q^(j+1)) := by rw [relation]
        _ = (1-q^(n-k)) * (∏ j ∈ Finset.range k, (1-q^(n-j))) := by rw [mul_assoc, ih (by omega)]
        _ = (∏ j ∈ Finset.range k, (1-q^(n-j))) * (1-q^(n-k)) := by ring

end ProjectEulerStatements.GaussianBinomial
