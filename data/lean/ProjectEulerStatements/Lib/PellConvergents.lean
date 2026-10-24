import ProjectEulerStatements.Lib.SqrtPeriods
import ProjectEulerStatements.Lib.PellMinimum

/-! Integer continuant norms along the square-root state orbit. -/
namespace ProjectEulerStatements.PellConvergents
open SqrtReducedStates
set_option Elab.async false

structure Convergents where
  olderP : Int
  currentP : Int
  olderQ : Int
  currentQ : Int

def initial : Convergents := ⟨0, 1, 1, 0⟩
def advance (a : Int) (values : Convergents) : Convergents :=
  ⟨values.currentP, a * values.currentP + values.olderP,
   values.currentQ, a * values.currentQ + values.olderQ⟩

def convergents (n : Nat) : Nat → Convergents
  | 0 => initial
  | index + 1 => advance (coefficient (Nat.sqrt n) (trajectory n index)) (convergents n index)

def norm (n p q : Int) : Int := p * p - n * q * q
def mixed (n : Int) (values : Convergents) : Int :=
  values.currentP * values.olderP - n * values.currentQ * values.olderQ
def determinant (values : Convergents) : Int :=
  values.currentP * values.olderQ - values.olderP * values.currentQ

structure Invariant (n : Int) (state : State) (sign : Int) (values : Convergents) : Prop where
  current : norm n values.currentP values.currentQ = sign * state.2
  cross : mixed n values = -sign * state.1
  older : state.2 * norm n values.olderP values.olderQ = sign * (state.1 * state.1 - n)

theorem norm_advance (n a : Int) (values : Convergents) :
    norm n (advance a values).currentP (advance a values).currentQ =
      a * a * norm n values.currentP values.currentQ + 2 * a * mixed n values +
        norm n values.olderP values.olderQ := by
  dsimp [advance, norm, mixed]
  ring

theorem mixed_advance (n a : Int) (values : Convergents) :
    mixed n (advance a values) = a * norm n values.currentP values.currentQ + mixed n values := by
  dsimp [advance, norm, mixed]
  ring

theorem determinant_advance (a : Int) (values : Convergents) :
    determinant (advance a values) = -determinant values := by
  dsimp [advance, determinant]
  ring

/-- The three quadratic identities advance using only the exact state product and a nonzero d. -/
theorem invariant_advance (n a sign : Int) (state next : State) (values : Convergents)
    (valid : Invariant n state sign values) (nonzero : state.2 ≠ 0)
    (nextM : state.2 * a - state.1 = next.1) (product : state.2 * next.2 = n - next.1 ^ 2) :
    Invariant n next (-sign) (advance a values) := by
  constructor
  · apply mul_left_cancel₀ nonzero
    calc
      state.2 * norm n (advance a values).currentP (advance a values).currentQ =
          state.2 * (a * a * norm n values.currentP values.currentQ + 2 * a * mixed n values) +
            state.2 * norm n values.olderP values.olderQ := by rw [norm_advance]; ring
      _ = state.2 * (a * a * (sign * state.2) + 2 * a * (-sign * state.1)) +
          sign * (state.1 * state.1 - n) := by rw [valid.current, valid.cross, valid.older]
      _ = sign * ((state.2 * a - state.1) ^ 2 - n) := by ring
      _ = -sign * (n - next.1 ^ 2) := by rw [nextM]; ring
      _ = state.2 * (-sign * next.2) := by rw [← product]; ring
  · rw [mixed_advance, valid.current, valid.cross, ← nextM]
    ring
  · change next.2 * norm n values.currentP values.currentQ = -sign * (next.1 * next.1 - n)
    rw [valid.current]
    calc
      next.2 * (sign * state.2) = sign * (state.2 * next.2) := by ring
      _ = sign * (n - next.1 ^ 2) := by rw [product]
      _ = -sign * (next.1 * next.1 - n) := by ring

theorem trajectory_product (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    (trajectory n index).2 * (trajectory n (index + 1)).2 =
      (n : Int) - (trajectory n (index + 1)).1 ^ 2 := by
  cases index with
  | zero =>
      have firstState : trajectory n 1 = first n (Nat.sqrt n) := by
        simpa using trajectory_succ n 0
      rw [firstState]
      simp [trajectory, first]
  | succ index =>
      have product := next_product (trajectory_reduced n (index + 1) (by omega) nonsquare)
      rw [trajectory_step] at product
      exact product

theorem convergents_invariant (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    Invariant n (trajectory n index) ((-1 : Int) ^ index) (convergents n index) := by
  induction index with
  | zero => constructor <;> simp [trajectory, convergents, initial, norm, mixed]
  | succ index ih =>
      have nextM := congrArg Prod.fst (trajectory_step n index)
      have next := invariant_advance n (coefficient (Nat.sqrt n) (trajectory n index))
        ((-1 : Int) ^ index) (trajectory n index) (trajectory n (index + 1)) (convergents n index)
        ih (ne_of_gt (trajectory_denominator_positive n index nonsquare)) nextM
        (trajectory_product n index nonsquare)
      simpa only [convergents, pow_succ, mul_neg_one] using next

theorem convergents_determinant (n index : Nat) :
    determinant (convergents n index) = (-1 : Int) ^ index := by
  induction index with
  | zero => rfl
  | succ index ih => rw [convergents, determinant_advance, ih]; simp [pow_succ]

theorem trajectory_periodic (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (positive : 0 < index) : trajectory n (index + length n) = trajectory n index := by
  cases index with
  | zero => omega
  | succ index =>
      rw [show index.succ + length n = (index + length n) + 1 by omega,
        trajectory_succ, trajectory_succ, length_of_nonsquare n nonsquare,
        Function.iterate_add_apply, period_returns]

theorem trajectory_terminal (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    trajectory n (length n) = terminal (Nat.sqrt n) := by
  rw [show length n = (length n - 1) + 1 by have := length_positive n nonsquare; omega,
    trajectory_succ, length_of_nonsquare n nonsquare, terminal_at_period]

/-- Two periods suffice for norm one, independently of the parity of the first period. -/
theorem norm_at_twice_period (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    norm n (convergents n (2 * length n)).currentP (convergents n (2 * length n)).currentQ = 1 := by
  have terminalState : trajectory n (2 * length n) = terminal (Nat.sqrt n) := by
    rw [show 2 * length n = length n + length n by omega,
      trajectory_periodic n (length n) nonsquare (length_positive n nonsquare),
      trajectory_terminal n nonsquare]
  have equation := (convergents_invariant n (2 * length n) nonsquare).current
  rw [terminalState] at equation
  simpa [pow_mul, terminal] using equation

theorem exists_hit (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    ∃ index : Nat, 0 < index ∧
      norm n (convergents n index).currentP (convergents n index).currentQ = 1 :=
  ⟨2 * length n, by have := length_positive n nonsquare; omega, norm_at_twice_period n nonsquare⟩

def firstHit (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) : Nat :=
  Nat.find (exists_hit n nonsquare)

theorem firstHit_positive (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    0 < firstHit n nonsquare := (Nat.find_spec (exists_hit n nonsquare)).1

theorem firstHit_norm (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    norm n (convergents n (firstHit n nonsquare)).currentP
      (convergents n (firstHit n nonsquare)).currentQ = 1 :=
  (Nat.find_spec (exists_hit n nonsquare)).2

theorem firstHit_le_twice_period (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    firstHit n nonsquare ≤ 2 * length n :=
  Nat.find_min' (exists_hit n nonsquare)
    ⟨by have := length_positive n nonsquare; omega, norm_at_twice_period n nonsquare⟩

theorem before_firstHit (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (positive : 0 < index) (before : index < firstHit n nonsquare) :
    norm n (convergents n index).currentP (convergents n index).currentQ ≠ 1 := by
  intro hit
  have minimal : firstHit n nonsquare ≤ index :=
    Nat.find_min' (exists_hit n nonsquare) ⟨positive, hit⟩
  omega

/-- All noninitial continuants have positive coordinates and nonnegative predecessors. -/
theorem convergents_positive (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (positive : 0 < index) :
    0 < (convergents n index).olderP ∧ 0 < (convergents n index).currentP ∧
    0 ≤ (convergents n index).olderQ ∧ 0 < (convergents n index).currentQ ∧
    (convergents n index).olderP ≤ (convergents n index).currentP ∧
    (convergents n index).olderQ ≤ (convergents n index).currentQ := by
  cases index with
  | zero => omega
  | succ index =>
      induction index with
      | zero =>
          have root := (sqrt_bounds n nonsquare).root_positive
          simpa [convergents, advance, initial, coefficient, trajectory] using
            (show (0 : Int) < 1 ∧ 0 < Nat.sqrt n ∧ 0 ≤ 0 ∧ 0 < 1 ∧
                1 ≤ Nat.sqrt n ∧ (0 : Int) ≤ 1 by omega)
      | succ index ih =>
          have previous := ih (by omega)
          have coefficientPos := coefficient_positive
            (trajectory_reduced n (index + 1) (by omega) nonsquare)
          change 0 < (convergents n (index + 1)).currentP ∧
            0 < coefficient (Nat.sqrt n) (trajectory n (index + 1)) *
              (convergents n (index + 1)).currentP + (convergents n (index + 1)).olderP ∧
            0 ≤ (convergents n (index + 1)).currentQ ∧
            0 < coefficient (Nat.sqrt n) (trajectory n (index + 1)) *
              (convergents n (index + 1)).currentQ + (convergents n (index + 1)).olderQ ∧
            (convergents n (index + 1)).currentP ≤
              coefficient (Nat.sqrt n) (trajectory n (index + 1)) *
                (convergents n (index + 1)).currentP + (convergents n (index + 1)).olderP ∧
            (convergents n (index + 1)).currentQ ≤
              coefficient (Nat.sqrt n) (trajectory n (index + 1)) *
                (convergents n (index + 1)).currentQ + (convergents n (index + 1)).olderQ
          rcases previous with ⟨olderP, currentP, olderQ, currentQ, _, _⟩
          refine ⟨currentP, ?_, by omega, ?_, ?_, ?_⟩ <;>
            nlinarith [mul_nonneg (by omega : 0 ≤ coefficient (Nat.sqrt n)
              (trajectory n (index + 1)) - 1) currentP.le,
              mul_nonneg (by omega : 0 ≤ coefficient (Nat.sqrt n)
                (trajectory n (index + 1)) - 1) currentQ.le]

/-- A first norm-one convergent is a positive solution, so the reference minimum is no larger. -/
theorem minimum_le_firstHit (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    (PellMinimum.minimum n : Int) ≤ (convergents n (firstHit n nonsquare)).currentP := by
  let values := convergents n (firstHit n nonsquare)
  have positive := convergents_positive n (firstHit n nonsquare) nonsquare
    (firstHit_positive n nonsquare)
  have castP : (values.currentP.toNat : Int) = values.currentP :=
    Int.toNat_of_nonneg positive.2.1.le
  have castQ : (values.currentQ.toNat : Int) = values.currentQ :=
    Int.toNat_of_nonneg positive.2.2.2.1.le
  have solution : values.currentP.toNat * values.currentP.toNat =
      n * values.currentQ.toNat * values.currentQ.toNat + 1 := by
    have equation : (values.currentP.toNat : Int) * values.currentP.toNat =
        (n : Int) * values.currentQ.toNat * values.currentQ.toNat + 1 := by
      rw [castP, castQ]
      have normOne := firstHit_norm n nonsquare
      change norm n values.currentP values.currentQ = 1 at normOne
      dsimp [norm] at normOne
      omega
    exact_mod_cast equation
  have yPositive : 1 ≤ values.currentQ.toNat := by
    have := positive.2.2.2.1
    change 0 < values.currentQ at this
    omega
  have minimal := PellMinimum.minimum_le n values.currentP.toNat values.currentQ.toNat
    nonsquare yPositive solution
  have castMinimal : (PellMinimum.minimum n : Int) ≤ values.currentP.toNat := by
    exact_mod_cast minimal
  simpa only [castP] using castMinimal

end ProjectEulerStatements.PellConvergents
