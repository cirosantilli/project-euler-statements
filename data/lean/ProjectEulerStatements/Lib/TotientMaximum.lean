import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Least totient-ratio maximizers are squarefree products of consecutive smallest primes. -/
namespace ProjectEulerStatements.TotientMaximum
set_option Elab.async false

def ratio (n : Nat) : ℚ := (n : ℚ) / n.totient

theorem ratio_pos (n : Nat) (positive : 0 < n) : 0 < ratio n :=
  div_pos (by exact_mod_cast positive) (by exact_mod_cast Nat.totient_pos.mpr positive)

theorem ratio_lt_iff (a b : Nat) (aPositive : 0 < a) (bPositive : 0 < b) :
    ratio a < ratio b ↔ a * b.totient < b * a.totient := by
  have aPhi : (0 : ℚ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr aPositive
  have bPhi : (0 : ℚ) < b.totient := by exact_mod_cast Nat.totient_pos.mpr bPositive
  rw [ratio, ratio, div_lt_div_iff₀ aPhi bPhi]
  exact_mod_cast Iff.rfl

theorem ratio_eq_iff (a b : Nat) (aPositive : 0 < a) (bPositive : 0 < b) :
    ratio a = ratio b ↔ a * b.totient = b * a.totient := by
  have aPhi : (a.totient : ℚ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr aPositive).ne'
  have bPhi : (b.totient : ℚ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr bPositive).ne'
  rw [ratio, ratio, div_eq_div_iff aPhi bPhi]
  exact_mod_cast Iff.rfl

structure LeastMaximum (limit value : Nat) : Prop where
  positive : 0 < value
  bounded : value ≤ limit
  dominates : ∀ n, 0 < n → n ≤ limit → ratio n ≤ ratio value
  least : ∀ n, 0 < n → n ≤ limit → ratio n = ratio value → value ≤ n

variable {limit value : Nat}

theorem new_prime_improves (p n : Nat) (prime : Nat.Prime p) (positive : 0 < n)
    (absent : ¬ p ∣ n) : ratio n < ratio (p * n) := by
  apply (ratio_lt_iff n (p * n) positive (Nat.mul_pos prime.pos positive)).mpr
  rw [Nat.totient_mul_of_prime_of_not_dvd prime absent]
  have smaller : p - 1 < p := Nat.sub_lt prime.pos (by decide)
  have scaled := Nat.mul_lt_mul_of_pos_right smaller
    (Nat.mul_pos positive (Nat.totient_pos.mpr positive))
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using scaled

theorem exchange_improves (p q n : Nat) (primeP : Nat.Prime p) (primeQ : Nat.Prime q)
    (positive : 0 < n) (smaller : p < q) (absentP : ¬ p ∣ n) (absentQ : ¬ q ∣ n) :
    ratio (q * n) < ratio (p * n) := by
  apply (ratio_lt_iff (q * n) (p * n)
    (Nat.mul_pos primeQ.pos positive) (Nat.mul_pos primeP.pos positive)).mpr
  rw [Nat.totient_mul_of_prime_of_not_dvd primeP absentP,
    Nat.totient_mul_of_prime_of_not_dvd primeQ absentQ]
  have coefficient : q * (p - 1) < p * (q - 1) := by
    have pPred := Nat.sub_add_cancel primeP.one_le
    have qPred := Nat.sub_add_cancel primeQ.one_le
    nlinarith
  have scaled := Nat.mul_lt_mul_of_pos_right coefficient
    (Nat.mul_pos positive (Nat.totient_pos.mpr positive))
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using scaled

theorem LeastMaximum.squarefree (maximum : LeastMaximum limit value) : Squarefree value := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p prime squareDivides
  obtain ⟨k, factor⟩ := squareDivides
  have decomposition : value = p * (p * k) := by rw [factor]; ring
  have positive : 0 < p * k := by
    have := maximum.positive
    rw [decomposition] at this
    exact Nat.pos_of_mul_pos_left this
  have smaller : p * k < value := by
    rw [decomposition]
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right prime.one_lt positive
  have phi : value.totient = p * (p * k).totient := by
    rw [decomposition, Nat.totient_mul_of_prime_of_dvd prime (dvd_mul_right p k)]
  have same : ratio (p * k) = ratio value := by
    apply (ratio_eq_iff _ _ positive maximum.positive).mpr
    rw [phi, decomposition]
    ring
  have minimal := maximum.least (p * k) positive
    ((Nat.le_of_lt smaller).trans maximum.bounded) same
  omega

theorem LeastMaximum.downward (maximum : LeastMaximum limit value)
    (p q : Nat) (primeP : Nat.Prime p) (primeQ : Nat.Prime q)
    (smaller : p < q) (divides : q ∣ value) : p ∣ value := by
  by_contra absent
  obtain ⟨k, factor⟩ := divides
  have positive : 0 < k := by
    have := maximum.positive
    rw [factor] at this
    exact Nat.pos_of_mul_pos_left this
  have absentP : ¬ p ∣ k := fun h => absent (h.trans (by rw [factor]; exact dvd_mul_left k q))
  have absentQ : ¬ q ∣ k := by
    intro h
    apply (Nat.squarefree_iff_prime_squarefree.mp maximum.squarefree q primeQ)
    rw [factor]
    exact mul_dvd_mul_left q h
  have improved := exchange_improves p q k primeP primeQ positive smaller absentP absentQ
  have bounded : p * k ≤ limit := by
    have smallerValue : p * k < value := by
      rw [factor]
      exact Nat.mul_lt_mul_of_pos_right smaller positive
    exact le_trans (Nat.le_of_lt smallerValue) maximum.bounded
  have dominated := maximum.dominates (p * k) (Nat.mul_pos primeP.pos positive) bounded
  rw [factor] at dominated
  exact (not_lt_of_ge dominated) improved

theorem squarefree_dvd_of_primes (a b : Nat) (squarefree : Squarefree a) (positive : 0 < b)
    (included : ∀ p, Nat.Prime p → p ∣ a → p ∣ b) : a ∣ b := by
  have subset : a.primeFactors ⊆ b.primeFactors := by
    intro p member
    have prime := Nat.prime_of_mem_primeFactors member
    exact Nat.mem_primeFactors.mpr
      ⟨prime, included p prime (Nat.dvd_of_mem_primeFactors member), positive.ne'⟩
  rw [← Nat.prod_primeFactors_of_squarefree squarefree]
  exact (Finset.prod_dvd_prod_of_subset _ _ id subset).trans (Nat.prod_primeFactors_dvd b)

structure PrimePrefix (value cursor : Nat) : Prop where
  squarefree : Squarefree value
  factors : ∀ p, Nat.Prime p → (p ∣ value ↔ p < cursor)

theorem prefix_eq_maximum (limit product cursor value : Nat)
    (positive : 0 < product) (bounded : product ≤ limit) (shape : PrimePrefix product cursor)
    (stopped : limit < product * cursor) (maximum : LeastMaximum limit value) :
    product = value := by
  have productDivides : product ∣ value := by
    apply squarefree_dvd_of_primes product value shape.squarefree maximum.positive
    intro p prime divides
    by_contra absent
    have below := (shape.factors p prime).mp divides
    have valueDivides : value ∣ product := by
      apply squarefree_dvd_of_primes value product maximum.squarefree positive
      intro q primeQ dividesQ
      have earlier : q < p := by
        by_contra tooLarge
        have different : q ≠ p := fun same => absent (same ▸ dividesQ)
        have less : p < q := by omega
        exact absent (maximum.downward p q prime primeQ less dividesQ)
      exact (shape.factors q primeQ).mpr (by omega)
    have coprime : Nat.Coprime p value := prime.coprime_iff_not_dvd.mpr absent
    have multiplied : p * value ∣ product := coprime.mul_dvd_of_dvd_of_dvd divides valueDivides
    have candidateBound : p * value ≤ limit := (Nat.le_of_dvd positive multiplied).trans bounded
    exact (not_lt_of_ge (maximum.dominates _ (Nat.mul_pos prime.pos maximum.positive)
      candidateBound)) (new_prime_improves p value prime maximum.positive absent)
  apply Nat.dvd_antisymm productDivides
  apply squarefree_dvd_of_primes value product maximum.squarefree positive
  intro p prime divides
  by_contra absent
  have later : cursor ≤ p := by
    by_contra tooEarly
    exact absent ((shape.factors p prime).mpr (by omega))
  have coprime : Nat.Coprime product p := (prime.coprime_iff_not_dvd.mpr absent).symm
  have multiplied : product * p ∣ value := coprime.mul_dvd_of_dvd_of_dvd productDivides divides
  have lower := Nat.le_of_dvd maximum.positive multiplied
  have monotone := Nat.mul_le_mul_left product later
  exact (not_lt_of_ge (monotone.trans (lower.trans maximum.bounded))) stopped

end ProjectEulerStatements.TotientMaximum
