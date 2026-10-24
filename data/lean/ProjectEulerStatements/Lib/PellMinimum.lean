import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Sqrt

/-! A computable least positive Pell solution with a proved existence witness. -/
namespace ProjectEulerStatements.PellMinimum
set_option Elab.async false

def candidate (d y : Nat) : Nat := Nat.sqrt (d * y * y + 1)
def Qualifies (d y : Nat) : Prop :=
  1 ≤ y ∧ candidate d y * candidate d y = d * y * y + 1

instance (d y : Nat) : Decidable (Qualifies d y) := by unfold Qualifies; infer_instance

theorem nonsquare_int (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    ¬ IsSquare (d : Int) := by
  intro square
  obtain ⟨root, same⟩ := Int.isSquare_natCast_iff.mp square
  have rootEq : root = Nat.sqrt d := Nat.eq_sqrt.mpr ⟨by nlinarith, by nlinarith⟩
  apply nonsquare
  rw [← rootEq]
  nlinarith

theorem nonsquare_two_le (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) : 2 ≤ d := by
  have notZero : d ≠ 0 := by rintro rfl; exact nonsquare rfl
  have notOne : d ≠ 1 := by rintro rfl; exact nonsquare rfl
  omega

theorem candidate_eq (d x y : Nat) (solution : x * x = d * y * y + 1) : candidate d y = x := by
  exact (Nat.eq_sqrt.mpr ⟨by nlinarith, by nlinarith⟩).symm

/-- Pell existence supplies a positive natural y accepted by the reference's exact square test. -/
theorem exists_qualifies (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    ∃ y, Qualifies d y := by
  have positive := nonsquare_two_le d nonsquare
  obtain ⟨solution, xPositive, yPositive⟩ := Pell.Solution₁.exists_pos_of_not_isSquare
    (by exact_mod_cast (show 0 < d by omega)) (nonsquare_int d nonsquare)
  let x := solution.x.toNat
  let y := solution.y.toNat
  have castX : (x : Int) = solution.x := Int.toNat_of_nonneg (by omega)
  have castY : (y : Int) = solution.y := Int.toNat_of_nonneg (by omega)
  have yNat : 0 < y := by exact_mod_cast (show (0 : Int) < y by simpa only [castY] using yPositive)
  have equation : x * x = d * y * y + 1 := by
    have prop : solution.x * solution.x = (d : Int) * solution.y * solution.y + 1 := by
      nlinarith [solution.prop]
    rw [← castX, ← castY] at prop
    exact_mod_cast prop
  refine ⟨y, by omega, ?_⟩
  rw [candidate_eq d x y equation]
  exact equation

def firstY (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) : Nat :=
  Nat.find (exists_qualifies d nonsquare)

theorem firstY_qualifies (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    Qualifies d (firstY d nonsquare) := Nat.find_spec (exists_qualifies d nonsquare)

theorem firstY_le (d y : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) (accepted : Qualifies d y) :
    firstY d nonsquare ≤ y := Nat.find_min' (exists_qualifies d nonsquare) accepted

theorem before_firstY (d y : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d)
    (positive : 1 ≤ y) (before : y < firstY d nonsquare) :
    candidate d y * candidate d y ≠ d * y * y + 1 := by
  intro accepted
  have minimal := firstY_le d y nonsquare ⟨positive, accepted⟩
  omega

def minimum (d : Nat) : Nat :=
  if square : Nat.sqrt d * Nat.sqrt d = d then 0 else candidate d (firstY d square)

theorem minimum_of_square (d : Nat) (square : Nat.sqrt d * Nat.sqrt d = d) : minimum d = 0 := by
  simp only [minimum, dif_pos square]

theorem minimum_of_nonsquare (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    minimum d = candidate d (firstY d nonsquare) := by simp only [minimum, dif_neg nonsquare]

theorem minimum_solution (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    minimum d * minimum d = d * firstY d nonsquare * firstY d nonsquare + 1 := by
  rw [minimum_of_nonsquare d nonsquare]
  exact (firstY_qualifies d nonsquare).2

theorem minimum_positive (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) : 1 < minimum d := by
  have accepted := firstY_qualifies d nonsquare
  have equation := minimum_solution d nonsquare
  have positive := nonsquare_two_le d nonsquare
  have squareY : 1 ≤ firstY d nonsquare * firstY d nonsquare :=
    by simpa using Nat.mul_le_mul accepted.1 accepted.1
  have scaled : 2 ≤ d * (firstY d nonsquare * firstY d nonsquare) :=
    by simpa using Nat.mul_le_mul positive squareY
  nlinarith

theorem candidate_mono (d left right : Nat) (ordered : left ≤ right) :
    candidate d left ≤ candidate d right := by
  apply Nat.sqrt_le_sqrt
  have square := Nat.mul_self_le_mul_self ordered
  have scaled := Nat.mul_le_mul_left d square
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right scaled 1

/-- The first accepted y also gives the least x among all positive Pell solutions. -/
theorem minimum_le (d x y : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d)
    (positive : 1 ≤ y) (solution : x * x = d * y * y + 1) : minimum d ≤ x := by
  have rootEq := candidate_eq d x y solution
  have accepted : Qualifies d y := ⟨positive, by simpa only [rootEq] using solution⟩
  rw [minimum_of_nonsquare d nonsquare, ← rootEq]
  exact candidate_mono d _ _ (firstY_le d y nonsquare accepted)

def fundamentalSolution (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    Pell.Solution₁ (d : Int) :=
  Pell.Solution₁.mk (minimum d) (firstY d nonsquare) (by
    have equation : (minimum d : Int) * minimum d =
        (d : Int) * firstY d nonsquare * firstY d nonsquare + 1 := by
      exact_mod_cast minimum_solution d nonsquare
    nlinarith)

/-- The searched minimum is the fundamental Pell solution, allowing either sign of y. -/
theorem minimum_fundamental (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    Pell.IsFundamental (fundamentalSolution d nonsquare) := by
  refine ⟨?_, ?_, ?_⟩
  · change (1 : Int) < minimum d
    exact_mod_cast minimum_positive d nonsquare
  · change (0 : Int) < firstY d nonsquare
    exact_mod_cast (show 0 < firstY d nonsquare by have := (firstY_qualifies d nonsquare).1; omega)
  · intro other positive
    have xCast : (other.x.toNat : Int) = other.x := Int.toNat_of_nonneg (by omega)
    have yNonzero := Pell.Solution₁.y_ne_zero_of_one_lt_x positive
    have yPositive : 0 < other.y.natAbs := Int.natAbs_pos.mpr yNonzero
    have equation : other.x.toNat * other.x.toNat = d * other.y.natAbs * other.y.natAbs + 1 := by
      have naturalY : (other.y.natAbs : Int) ^ 2 = other.y ^ 2 := by simp
      have prop : (other.x.toNat : Int) * other.x.toNat =
          (d : Int) * other.y.natAbs * other.y.natAbs + 1 := by
        rw [xCast]
        nlinarith [other.prop]
      exact_mod_cast prop
    change (minimum d : Int) ≤ other.x
    rw [← xCast]
    exact_mod_cast minimum_le d other.x.toNat other.y.natAbs nonsquare (by omega) equation

end ProjectEulerStatements.PellMinimum
