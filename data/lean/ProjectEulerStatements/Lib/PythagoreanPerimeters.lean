import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.NormNum

/-! Positive, canonical Euclid parameters for unordered integer right triangles.
The classification is derived from Mathlib's proved primitive classification. -/
namespace ProjectEulerStatements.PythagoreanPerimeters

set_option Elab.async false

def Parameters (m n k : Nat) : Prop :=
  0 < n ∧ n < m ∧ 0 < k ∧ Nat.Coprime m n ∧ (m - n) % 2 = 1

instance (m n k : Nat) : Decidable (Parameters m n k) := by
  unfold Parameters
  infer_instance

def oddLeg (m n k : Nat) : Nat := k * (m ^ 2 - n ^ 2)
def evenLeg (m n k : Nat) : Nat := k * (2 * m * n)
def hypotenuse (m n k : Nat) : Nat := k * (m ^ 2 + n ^ 2)

def sides (m n k : Nat) : Nat × Nat × Nat :=
  (min (oddLeg m n k) (evenLeg m n k),
    max (oddLeg m n k) (evenLeg m n k), hypotenuse m n k)

def Canonical (a b c : Nat) : Prop := 0 < a ∧ a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2

/-- Choosing the odd primitive leg removes both the leg-swap and sign ambiguities
from Mathlib's integer parameterization. -/
theorem primitive_oriented {x y z : Int} (triple : PythagoreanTriple x y z)
    (coprime : Int.gcd x y = 1) (xPositive : 0 < x) (yPositive : 0 < y)
    (zPositive : 0 < z) (odd : x % 2 = 1) :
    ∃ m n : Nat, 0 < n ∧ n < m ∧ Nat.Coprime m n ∧ (m - n) % 2 = 1 ∧
      x = (m : Int) ^ 2 - (n : Int) ^ 2 ∧ y = 2 * (m : Int) * n ∧
      z = (m : Int) ^ 2 + (n : Int) ^ 2 := by
  obtain ⟨m, n, xEq, yEq, zEq, co, parity, mNonnegative⟩ :=
    triple.coprime_classification' coprime odd zPositive
  have mPositive : 0 < m := by nlinarith [sq_nonneg n]
  have nPositive : 0 < n := by
    by_contra nonpositive
    have product := mul_nonpos_of_nonneg_of_nonpos mNonnegative (show n ≤ 0 by omega)
    nlinarith
  have ordered : n < m := by nlinarith
  have mCast : (m.toNat : Int) = m := Int.toNat_of_nonneg mNonnegative
  have nCast : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
  have coNat : Nat.Coprime m.toNat n.toNat := by
    change Nat.gcd m.toNat n.toNat = 1
    rw [← Int.gcd_natCast_natCast, mCast, nCast]
    exact co
  refine ⟨m.toNat, n.toNat, by omega, by omega, coNat, ?_, ?_, ?_, ?_⟩
  · rcases parity with parity | parity <;> omega
  · simpa only [mCast, nCast] using xEq
  · simpa only [mCast, nCast] using yEq
  · simpa only [mCast, nCast] using zEq

theorem primitive_classification {x y z : Int} (triple : PythagoreanTriple x y z)
    (coprime : Int.gcd x y = 1) (xPositive : 0 < x) (yPositive : 0 < y)
    (zPositive : 0 < z) :
    ∃ m n : Nat, 0 < n ∧ n < m ∧ Nat.Coprime m n ∧ (m - n) % 2 = 1 ∧
      ((x = (m : Int) ^ 2 - (n : Int) ^ 2 ∧ y = 2 * (m : Int) * n) ∨
        (y = (m : Int) ^ 2 - (n : Int) ^ 2 ∧ x = 2 * (m : Int) * n)) ∧
      z = (m : Int) ^ 2 + (n : Int) ^ 2 := by
  rcases triple.even_odd_of_coprime coprime with parity | parity
  · obtain ⟨m, n, positive, ordered, co, opposite, yEq, xEq, zEq⟩ :=
      primitive_oriented triple.symm (by simpa [Int.gcd_comm] using coprime)
        yPositive xPositive zPositive parity.2
    exact ⟨m, n, positive, ordered, co, opposite, Or.inr ⟨yEq, xEq⟩, zEq⟩
  · obtain ⟨m, n, positive, ordered, co, opposite, xEq, yEq, zEq⟩ :=
      primitive_oriented triple coprime xPositive yPositive zPositive parity.1
    exact ⟨m, n, positive, ordered, co, opposite, Or.inl ⟨xEq, yEq⟩, zEq⟩

theorem parameter_parity (m n k : Nat) (parameters : Parameters m n k) :
    ((m : Int) % 2 = 0 ∧ (n : Int) % 2 = 1) ∨
      ((m : Int) % 2 = 1 ∧ (n : Int) % 2 = 0) := by
  rcases parameters with ⟨positive, ordered, _, _, opposite⟩
  omega

theorem primitive_coprime (m n k : Nat) (parameters : Parameters m n k) :
    Nat.Coprime (m ^ 2 - n ^ 2) (2 * m * n) := by
  have ordered := parameters.2.1
  have squareLe : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt ordered) 2
  have castOdd : ((m ^ 2 - n ^ 2 : Nat) : Int) = (m : Int) ^ 2 - (n : Int) ^ 2 := by
    rw [Int.natCast_sub squareLe]
    norm_cast
  have castEven : ((2 * m * n : Nat) : Int) = 2 * (m : Int) * n := by norm_cast
  have classified : PythagoreanTriple ((m : Int) ^ 2 - (n : Int) ^ 2)
      (2 * (m : Int) * n) ((m : Int) ^ 2 + (n : Int) ^ 2) ∧
      Int.gcd ((m : Int) ^ 2 - (n : Int) ^ 2) (2 * (m : Int) * n) = 1 := by
    apply PythagoreanTriple.coprime_classification.mpr
    refine ⟨(m : Int), (n : Int), Or.inl ⟨rfl, rfl⟩, Or.inl rfl, ?_,
      parameter_parity m n k parameters⟩
    simpa only [Int.gcd_natCast_natCast] using parameters.2.2.2.1
  have gcd := classified.2
  rw [← castOdd, ← castEven, Int.gcd_natCast_natCast] at gcd
  exact gcd

theorem primitive_odd (m n k : Nat) (parameters : Parameters m n k) :
    (m ^ 2 - n ^ 2) % 2 = 1 := by
  have squareLe : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt parameters.2.1) 2
  have parity (value : Nat) : value ^ 2 % 2 = value % 2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one value with residue | residue <;> simp [residue]
  have sum := congrArg (fun value : Nat => value % 2) (Nat.sub_add_cancel squareLe)
  dsimp only at sum
  rw [Nat.add_mod, parity n, parity m] at sum
  have opposite := parameters.2.2.2.2
  have ordered := parameters.2.1
  omega

theorem primitive_even (m n : Nat) : (2 * m * n) % 2 = 0 := by simp [Nat.mul_mod]

theorem legs_gcd (m n k : Nat) (parameters : Parameters m n k) :
    Nat.gcd (oddLeg m n k) (evenLeg m n k) = k := by
  simp only [oddLeg, evenLeg, Nat.gcd_mul_left, primitive_coprime m n k parameters,
    Nat.mul_one]

theorem sides_gcd (m n k : Nat) (parameters : Parameters m n k) :
    Nat.gcd (sides m n k).1 (sides m n k).2.1 = k := by
  unfold sides
  by_cases order : oddLeg m n k ≤ evenLeg m n k
  · simpa [min_eq_left order, max_eq_right order] using legs_gcd m n k parameters
  · simpa [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge order)),
      max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge order)), Nat.gcd_comm] using
      legs_gcd m n k parameters

theorem sides_perimeter (m n k : Nat) (parameters : Parameters m n k) :
    (sides m n k).1 + (sides m n k).2.1 + (sides m n k).2.2 = 2 * k * m * (m + n) := by
  have squareLe : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt parameters.2.1) 2
  have sum := Nat.sub_add_cancel squareLe
  simp only [sides, min_add_max, oddLeg, evenLeg, hypotenuse]
  nlinarith [congrArg (fun value => k * value) sum]

theorem sides_canonical (m n k : Nat) (parameters : Parameters m n k) :
    Canonical (sides m n k).1 (sides m n k).2.1 (sides m n k).2.2 := by
  have nPositive := parameters.1
  have ordered := parameters.2.1
  have kPositive := parameters.2.2.1
  have mPositive : 0 < m := by omega
  have squareLt : n ^ 2 < m ^ 2 := Nat.pow_lt_pow_left ordered (by decide)
  have squareLe := Nat.le_of_lt squareLt
  have oddPositive : 0 < m ^ 2 - n ^ 2 := Nat.sub_pos_of_lt squareLt
  have evenPositive : 0 < 2 * m * n := by positivity
  have oddParity := primitive_odd m n k parameters
  have evenParity := primitive_even m n
  have distinct : m ^ 2 - n ^ 2 ≠ 2 * m * n := by omega
  have castOdd : ((m ^ 2 - n ^ 2 : Nat) : Int) = (m : Int) ^ 2 - (n : Int) ^ 2 := by
    rw [Int.natCast_sub squareLe]
    norm_cast
  have py : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
    have identity : ((m : Int) ^ 2 - (n : Int) ^ 2) ^ 2 +
        (2 * (m : Int) * n) ^ 2 = ((m : Int) ^ 2 + (n : Int) ^ 2) ^ 2 := by ring
    rw [← castOdd] at identity
    exact_mod_cast identity
  have oddBelow : m ^ 2 - n ^ 2 < m ^ 2 + n ^ 2 := by
    have positive : 0 < n ^ 2 := Nat.pow_pos nPositive
    omega
  have evenBelow : 2 * m * n < m ^ 2 + n ^ 2 := by
    have positive : 0 < (m : Int) - (n : Int) := by omega
    have result : 2 * (m : Int) * n < (m : Int) ^ 2 + (n : Int) ^ 2 := by
      nlinarith [sq_pos_of_pos positive]
    exact_mod_cast result
  have scaledDistinct : oddLeg m n k ≠ evenLeg m n k := by
    intro equal
    exact distinct ((Nat.mul_left_cancel_iff kPositive).mp equal)
  have scaledOdd : 0 < oddLeg m n k := Nat.mul_pos kPositive oddPositive
  have scaledEven : 0 < evenLeg m n k := Nat.mul_pos kPositive evenPositive
  have scaledOddBelow : oddLeg m n k < hypotenuse m n k :=
    Nat.mul_lt_mul_of_pos_left oddBelow kPositive
  have scaledEvenBelow : evenLeg m n k < hypotenuse m n k :=
    Nat.mul_lt_mul_of_pos_left evenBelow kPositive
  have scaledPy : (oddLeg m n k) ^ 2 + (evenLeg m n k) ^ 2 = (hypotenuse m n k) ^ 2 := by
    unfold oddLeg evenLeg hypotenuse
    nlinarith [congrArg (fun value => k ^ 2 * value) py]
  unfold Canonical sides
  by_cases order : oddLeg m n k ≤ evenLeg m n k
  · simp only [min_eq_left order, max_eq_right order]
    exact ⟨scaledOdd, by omega, scaledEvenBelow, scaledPy⟩
  · simp only [min_eq_right (by omega : evenLeg m n k ≤ oddLeg m n k),
      max_eq_left (by omega : evenLeg m n k ≤ oddLeg m n k)]
    exact ⟨scaledEven, by omega, scaledOddBelow, by nlinarith [scaledPy]⟩

theorem canonical_parameters (a b c : Nat) (canonical : Canonical a b c) :
    ∃ m n k : Nat, Parameters m n k ∧ sides m n k = (a, b, c) := by
  have aPositive := canonical.1
  have bPositive : 0 < b := by have := canonical.2.1; omega
  have cPositive : 0 < c := by have := canonical.2.2.1; omega
  have triple : PythagoreanTriple (a : Int) (b : Int) (c : Int) := by
    unfold PythagoreanTriple
    exact_mod_cast (show a * a + b * b = c * c by simpa only [pow_two] using canonical.2.2.2)
  let k := Int.gcd (a : Int) (b : Int)
  have kPositive : 0 < k := by
    simpa [k] using Nat.gcd_pos_of_pos_left b aPositive
  let x := (a : Int) / k
  let y := (b : Int) / k
  let z := (c : Int) / k
  have xPositive : 0 < x := Int.ediv_pos_of_pos_of_dvd (by exact_mod_cast aPositive)
    (Int.natCast_nonneg k) (Int.gcd_dvd_left (a : Int) (b : Int))
  have yPositive : 0 < y := Int.ediv_pos_of_pos_of_dvd (by exact_mod_cast bPositive)
    (Int.natCast_nonneg k) (Int.gcd_dvd_right (a : Int) (b : Int))
  have zPositive : 0 < z := Int.ediv_pos_of_pos_of_dvd (by exact_mod_cast cPositive)
    (Int.natCast_nonneg k) triple.gcd_dvd
  have normalized : PythagoreanTriple x y z := triple.normalize
  have coprime : Int.gcd x y = 1 := Int.gcd_ediv_gcd_ediv_gcd kPositive
  have aScale : (a : Int) = (k : Int) * x :=
    (Int.mul_ediv_cancel' (Int.gcd_dvd_left (a : Int) (b : Int))).symm
  have bScale : (b : Int) = (k : Int) * y :=
    (Int.mul_ediv_cancel' (Int.gcd_dvd_right (a : Int) (b : Int))).symm
  have cScale : (c : Int) = (k : Int) * z := (Int.mul_ediv_cancel' triple.gcd_dvd).symm
  obtain ⟨m, n, nPositive, ordered, co, opposite, legs, hyp⟩ :=
    primitive_classification normalized coprime xPositive yPositive zPositive
  have parameters : Parameters m n k := ⟨nPositive, ordered, kPositive, co, opposite⟩
  have squareLe : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt ordered) 2
  have castOdd : ((oddLeg m n k : Nat) : Int) =
      (k : Int) * ((m : Int) ^ 2 - (n : Int) ^ 2) := by
    simp only [oddLeg, Int.natCast_mul, Int.natCast_sub squareLe, Int.natCast_pow]
  have castEven : ((evenLeg m n k : Nat) : Int) = (k : Int) * (2 * (m : Int) * n) := by
    simp [evenLeg]
  have cEq : c = hypotenuse m n k := by
    apply Int.natCast_inj.mp
    simpa only [hypotenuse, Int.natCast_mul, Int.natCast_add, Int.natCast_pow] using
      cScale.trans (congrArg (fun value => (k : Int) * value) hyp)
  refine ⟨m, n, k, parameters, ?_⟩
  rcases legs with ⟨xEq, yEq⟩ | ⟨yEq, xEq⟩
  · have aEq : a = oddLeg m n k := by
      apply Int.natCast_inj.mp
      rw [castOdd]
      exact aScale.trans (congrArg (fun value => (k : Int) * value) xEq)
    have bEq : b = evenLeg m n k := by
      apply Int.natCast_inj.mp
      rw [castEven]
      exact bScale.trans (congrArg (fun value => (k : Int) * value) yEq)
    simp only [sides, ← aEq, ← bEq, ← cEq,
      min_eq_left (Nat.le_of_lt canonical.2.1), max_eq_right (Nat.le_of_lt canonical.2.1)]
  · have bEq : b = oddLeg m n k := by
      apply Int.natCast_inj.mp
      rw [castOdd]
      exact bScale.trans (congrArg (fun value => (k : Int) * value) yEq)
    have aEq : a = evenLeg m n k := by
      apply Int.natCast_inj.mp
      rw [castEven]
      exact aScale.trans (congrArg (fun value => (k : Int) * value) xEq)
    simp only [sides, ← aEq, ← bEq, ← cEq,
      min_eq_right (Nat.le_of_lt canonical.2.1), max_eq_left (Nat.le_of_lt canonical.2.1)]

private theorem pair_of_min_max_eq (a b c d : Nat)
    (lower : min a b = min c d) (upper : max a b = max c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases first : a ≤ b <;> by_cases second : c ≤ d <;>
    simp only [min_def, max_def, first, second, if_true, if_false] at lower upper <;> omega

theorem parameters_unique (m n k m' n' k' : Nat)
    (parameters : Parameters m n k) (parameters' : Parameters m' n' k')
    (equal : sides m n k = sides m' n' k') : (m, n, k) = (m', n', k') := by
  have scale := congrArg (fun triangle : Nat × Nat × Nat => Nat.gcd triangle.1 triangle.2.1) equal
  change Nat.gcd (sides m n k).1 (sides m n k).2.1 =
    Nat.gcd (sides m' n' k').1 (sides m' n' k').2.1 at scale
  rw [sides_gcd m n k parameters, sides_gcd m' n' k' parameters'] at scale
  subst k'
  have kPositive := parameters.2.2.1
  have lower := congrArg (fun triangle : Nat × Nat × Nat => triangle.1) equal
  have upper := congrArg (fun triangle : Nat × Nat × Nat => triangle.2.1) equal
  have hyp := congrArg (fun triangle : Nat × Nat × Nat => triangle.2.2) equal
  change k * (m ^ 2 + n ^ 2) = k * (m' ^ 2 + n' ^ 2) at hyp
  have hypEqual := (Nat.mul_left_cancel_iff kPositive).mp hyp
  obtain aligned | crossed := pair_of_min_max_eq
    (oddLeg m n k) (evenLeg m n k) (oddLeg m' n' k) (evenLeg m' n' k) lower upper
  · have oddEqual := (Nat.mul_left_cancel_iff kPositive).mp aligned.1
    change m ^ 2 - n ^ 2 = m' ^ 2 - n' ^ 2 at oddEqual
    have firstSub := Nat.sub_add_cancel
      (Nat.pow_le_pow_left (Nat.le_of_lt parameters.2.1) 2)
    have secondSub := Nat.sub_add_cancel
      (Nat.pow_le_pow_left (Nat.le_of_lt parameters'.2.1) 2)
    have mSquare : m ^ 2 = m' ^ 2 := by omega
    have nSquare : n ^ 2 = n' ^ 2 := by omega
    have mEq := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp mSquare
    have nEq := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp nSquare
    exact Prod.ext mEq (Prod.ext nEq rfl)
  · have oddEven := (Nat.mul_left_cancel_iff kPositive).mp crossed.1
    change m ^ 2 - n ^ 2 = 2 * m' * n' at oddEven
    have odd := primitive_odd m n k parameters
    have even := primitive_even m' n'
    omega

/-- Every ordered positive triangle has exactly one positive scale and one
coprime opposite-parity Euclid parameter pair. -/
theorem canonical_unique (a b c : Nat) (canonical : Canonical a b c) :
    ∃! parameter : Nat × Nat × Nat,
      Parameters parameter.1 parameter.2.1 parameter.2.2 ∧
        sides parameter.1 parameter.2.1 parameter.2.2 = (a, b, c) := by
  obtain ⟨m, n, k, parameters, generated⟩ := canonical_parameters a b c canonical
  refine ⟨(m, n, k), ⟨parameters, generated⟩, ?_⟩
  rintro ⟨m', n', k'⟩ ⟨parameters', generated'⟩
  exact parameters_unique m' n' k' m n k parameters' parameters
    (generated'.trans generated.symm)

end ProjectEulerStatements.PythagoreanPerimeters
