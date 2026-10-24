import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integer invariants for the complete-quotient recurrence of a nonsquare square root. -/
namespace ProjectEulerStatements.SqrtReducedStates
set_option Elab.async false

abbrev State := Int × Int

structure Bounds (n root : Int) : Prop where
  root_nonneg : 0 ≤ root
  below : root ^ 2 < n
  above : n < (root + 1) ^ 2

def Reduced (n root : Int) (state : State) : Prop :=
  0 ≤ state.1 ∧ state.1 ≤ root ∧ 0 < state.2 ∧
    root - state.1 < state.2 ∧ state.2 ≤ root + state.1 ∧ state.2 ∣ n - state.1 ^ 2

instance (n root : Int) (state : State) : Decidable (Reduced n root state) := by
  unfold Reduced
  infer_instance

def coefficient (root : Int) (state : State) : Int := (root + state.1) / state.2

def step (n root : Int) (state : State) : State :=
  let offset := state.2 * coefficient root state - state.1
  (offset, (n - offset ^ 2) / state.2)

def inverse (n root : Int) (state : State) : State :=
  let denominator := (n - state.1 ^ 2) / state.2
  (denominator * ((root + state.1) / denominator) - state.1, denominator)

def first (n root : Int) : State := (root, n - root ^ 2)
def terminal (root : Int) : State := (root, 1)

theorem Bounds.root_positive {n root : Int} (bounds : Bounds n root) : 0 < root := by
  by_contra absent
  have zero : root = 0 := by have := bounds.root_nonneg; omega
  have low := bounds.below
  have high := bounds.above
  rw [zero] at low high
  norm_num at low high
  omega

theorem first_reduced {n root : Int} (bounds : Bounds n root) : Reduced n root (first n root) := by
  have positive := bounds.root_positive
  have low := bounds.below
  have high := bounds.above
  change 0 ≤ root ∧ root ≤ root ∧ 0 < n - root ^ 2 ∧
    root - root < n - root ^ 2 ∧ n - root ^ 2 ≤ root + root ∧ (n - root ^ 2) ∣ n - root ^ 2
  refine ⟨by omega, le_rfl, by omega, by omega, ?_, dvd_refl _⟩
  nlinarith

theorem terminal_reduced {n root : Int} (bounds : Bounds n root) :
    Reduced n root (terminal root) := by
  have positive := bounds.root_positive
  dsimp only [Reduced, terminal]
  exact ⟨by omega, le_rfl, by omega, by omega, by omega, one_dvd _⟩

theorem coefficient_positive {n root : Int} {state : State} (valid : Reduced n root state) :
    1 ≤ coefficient root state := by
  rcases valid with ⟨_, _, positive, _, upper, _⟩
  exact (Int.le_ediv_iff_mul_le positive).mpr (by simpa using upper)

theorem offset_bounds {n root : Int} {state : State} (valid : Reduced n root state) :
    0 < (step n root state).1 ∧ (step n root state).1 ≤ root ∧
      root - (step n root state).1 < state.2 ∧ state.2 ≤ root + (step n root state).1 := by
  have quotient := (Int.ediv_eq_iff_of_pos valid.2.2.1).mp
    (rfl : coefficient root state = coefficient root state)
  have positive := coefficient_positive valid
  rcases valid with ⟨offsetNonneg, offsetUpper, denominatorPositive, _, _, _⟩
  have scale : state.2 ≤ state.2 * coefficient root state := by
    nlinarith [mul_nonneg denominatorPositive.le (by omega : 0 ≤ coefficient root state - 1)]
  change 0 < state.2 * coefficient root state - state.1 ∧
    state.2 * coefficient root state - state.1 ≤ root ∧
    root - (state.2 * coefficient root state - state.1) < state.2 ∧
    state.2 ≤ root + (state.2 * coefficient root state - state.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra absent
    have small : state.2 ≤ state.1 := by omega
    nlinarith [quotient.2]
  · nlinarith [quotient.1]
  · nlinarith [quotient.2]
  · omega

theorem next_divides {n root : Int} {state : State} (valid : Reduced n root state) :
    state.2 ∣ n - (step n root state).1 ^ 2 := by
  obtain ⟨value, factored⟩ := valid.2.2.2.2.2
  refine ⟨value - coefficient root state * ((step n root state).1 - state.1), ?_⟩
  have sum : (step n root state).1 + state.1 = state.2 * coefficient root state := by simp [step]
  calc
    n - (step n root state).1 ^ 2 =
        (n - state.1 ^ 2) - ((step n root state).1 + state.1) *
          ((step n root state).1 - state.1) := by ring
    _ = state.2 * value - (state.2 * coefficient root state) *
        ((step n root state).1 - state.1) := by rw [factored, sum]
    _ = state.2 * (value - coefficient root state * ((step n root state).1 - state.1)) := by ring

theorem next_product {n root : Int} {state : State} (valid : Reduced n root state) :
    state.2 * (step n root state).2 = n - (step n root state).1 ^ 2 :=
  Int.mul_ediv_cancel' (next_divides valid)

/-- Exact divisibility and the two reduced inequalities are preserved by each source step. -/
theorem step_reduced {n root : Int} {state : State} (bounds : Bounds n root)
    (valid : Reduced n root state) :
    Reduced n root (step n root state) := by
  have offsets := offset_bounds valid
  have product := next_product valid
  have low := bounds.below
  have high := bounds.above
  have denominatorPositive := valid.2.2.1
  have numeratorPositive : 0 < n - (step n root state).1 ^ 2 := by
    nlinarith [bounds.root_nonneg]
  have nextPositive : 0 < (step n root state).2 := by nlinarith
  have nextLower : root - (step n root state).1 < (step n root state).2 := by
    by_contra absent
    have comparison : state.2 * (step n root state).2 ≤
        (root + (step n root state).1) * (root - (step n root state).1) :=
      mul_le_mul offsets.2.2.2 (by omega) nextPositive.le (by omega)
    nlinarith
  have nextUpper : (step n root state).2 ≤ root + (step n root state).1 := by
    by_contra absent
    have comparison : (root - (step n root state).1 + 1) * (root + (step n root state).1 + 1) ≤
        state.2 * (step n root state).2 :=
      mul_le_mul (by omega) (by omega) (by omega) denominatorPositive.le
    nlinarith
  refine ⟨offsets.1.le, offsets.2.1, nextPositive, nextLower, nextUpper, ?_⟩
  exact ⟨state.2, by nlinarith [product]⟩

theorem inverse_step {n root : Int} {state : State} (bounds : Bounds n root)
    (valid : Reduced n root state) :
    inverse n root (step n root state) = state := by
  have nextValid := step_reduced bounds valid
  have product := next_product valid
  have recoveredDenominator :
      (n - (step n root state).1 ^ 2) / (step n root state).2 = state.2 := by
    rw [← product, Int.mul_ediv_cancel _ (ne_of_gt nextValid.2.2.1)]
  have recoveredCoefficient :
      (root + (step n root state).1) / state.2 = coefficient root state := by
    apply (Int.ediv_eq_iff_of_pos valid.2.2.1).mpr
    dsimp only [step, Prod.fst]
    constructor <;> nlinarith [valid.2.1, valid.2.2.2.1]
  unfold inverse
  dsimp only
  rw [recoveredDenominator, recoveredCoefficient]
  apply Prod.ext
  · dsimp only [step, Prod.fst]
    ring
  · rfl

/-- Reduced states have unique predecessors, so a finite orbit cannot acquire a new tail. -/
theorem step_injective {n root : Int} {left right : State} (bounds : Bounds n root)
    (leftValid : Reduced n root left) (rightValid : Reduced n root right)
    (same : step n root left = step n root right) : left = right := by
  calc
    left = inverse n root (step n root left) := (inverse_step bounds leftValid).symm
    _ = inverse n root (step n root right) := congrArg (inverse n root) same
    _ = right := inverse_step bounds rightValid

theorem coefficient_terminal_iff {n root : Int} {state : State}
    (bounds : Bounds n root) (valid : Reduced n root state) :
    coefficient root state = 2 * root ↔ state = terminal root := by
  constructor
  · intro same
    have quotient := (Int.ediv_eq_iff_of_pos valid.2.2.1).mp
      (rfl : coefficient root state = coefficient root state)
    rw [same] at quotient
    have denominatorOne : state.2 = 1 := by
      by_contra different
      have strict : 0 < root * (state.2 - 1) :=
        mul_pos bounds.root_positive (by have := valid.2.2.1; omega)
      nlinarith [quotient.1, valid.2.1]
    apply Prod.ext
    · change state.1 = root
      rw [denominatorOne] at quotient
      nlinarith [quotient.1, valid.2.1]
    · exact denominatorOne
  · rintro rfl
    simp [coefficient, terminal, two_mul]

theorem step_terminal (n root : Int) : step n root (terminal root) = first n root := by
  simp [step, coefficient, terminal, first]

theorem step_initial (n root : Int) : step n root (0, 1) = first n root := by
  simp [step, coefficient, first]

end ProjectEulerStatements.SqrtReducedStates
