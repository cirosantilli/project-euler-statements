import ProjectEulerStatements.Lib.PellConvergents

/-! Positive Pell solutions descend through the integer continued-fraction bases. -/
namespace ProjectEulerStatements.PellConvergents
open SqrtReducedStates
set_option Elab.async false

/-- A convex quadratic on an integer interval is bounded by its endpoint bounds. -/
theorem quadratic_le_of_endpoints (a b c lo hi value bound : Int) (nonneg : 0 ≤ a)
    (lower : lo ≤ value) (upper : value ≤ hi)
    (atLo : a * lo * lo + b * lo + c ≤ bound)
    (atHi : a * hi * hi + b * hi + c ≤ bound) :
    a * value * value + b * value + c ≤ bound := by
  by_cases slope : a * (value + lo) + b ≤ 0
  · have product := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr lower) slope
    have identity : a * value * value + b * value + c - (a * lo * lo + b * lo + c) =
        (value - lo) * (a * (value + lo) + b) := by ring
    omega
  · have later : 0 ≤ a * (hi + value) + b := by
      have scaled := mul_nonneg nonneg (show 0 ≤ hi - lo by omega)
      nlinarith
    have product := mul_nonneg (sub_nonneg.mpr upper) later
    have identity : a * hi * hi + b * hi + c - (a * value * value + b * value + c) =
        (hi - value) * (a * (hi + value) + b) := by ring
    omega

/-- Norm at least minus one forces a nonnegative next remainder in a reduced Pell basis. -/
theorem remainder_nonnegative (root m d previous a nextM nextD r s : Int)
    (mNonneg : 0 ≤ m) (mUpper : m ≤ root) (dPositive : 0 < d)
    (dUpper : d ≤ root + m) (previousLower : root - m < previous)
    (aPositive : 1 ≤ a) (nextNonneg : 0 ≤ nextM) (nextUpper : nextM ≤ root)
    (nextLower : root - nextM < nextD) (dNextUpper : d ≤ root + nextM)
    (nextOffset : d * a = m + nextM)
    (recurrence : previous = d * a * a - 2 * m * a + nextD)
    (rPositive : 0 < r) (sPositive : 0 < s)
    (normLower : -1 ≤ d * r * r - 2 * m * r * s - previous * s * s) :
    0 ≤ r - a * s := by
  by_contra negative
  have interval : r ≤ a * s - 1 := by omega
  have previousPositive : 0 < previous := by omega
  have nextPositive : 0 < nextD := by omega
  have leftGap : d + 1 ≤ 2 * m + previous := by omega
  have rightGap : d + 1 ≤ 2 * nextM + nextD := by omega
  have atLo : d * 1 * 1 + (-2 * m * s) * 1 + (-previous * s * s) ≤ -2 := by
    by_cases one : s = 1
    · subst s
      have two : 2 ≤ a := by omega
      have scaled := mul_le_mul_of_nonneg_left two dPositive.le
      rw [nextOffset] at scaled
      nlinarith
    · have two : 2 ≤ s := by omega
      have square : 2 ≤ s * s := by nlinarith
      have scaled : previous + 1 ≤ previous * s * s := by
        calc
          previous + 1 ≤ previous * 2 := by omega
          _ ≤ previous * (s * s) := mul_le_mul_of_nonneg_left square previousPositive.le
          _ = previous * s * s := by ring
      have offset := mul_nonneg mNonneg (show 0 ≤ s - 1 by omega)
      nlinarith
  have atHi : d * (a * s - 1) * (a * s - 1) + (-2 * m * s) * (a * s - 1) +
      (-previous * s * s) ≤ -2 := by
    have expression : d * (a * s - 1) * (a * s - 1) + (-2 * m * s) * (a * s - 1) +
        (-previous * s * s) = d - 2 * nextM * s - nextD * s * s := by
      rw [recurrence, show nextM = d * a - m by omega]
      ring
    rw [expression]
    by_cases one : s = 1
    · subst s
      have two : 2 ≤ a := by omega
      have scaled := mul_le_mul_of_nonneg_left two dPositive.le
      rw [nextOffset] at scaled
      nlinarith
    · have two : 2 ≤ s := by omega
      have square : 2 ≤ s * s := by nlinarith
      have scaled : nextD + 1 ≤ nextD * s * s := by
        calc
          nextD + 1 ≤ nextD * 2 := by omega
          _ ≤ nextD * (s * s) := mul_le_mul_of_nonneg_left square nextPositive.le
          _ = nextD * s * s := by ring
      have offset := mul_nonneg nextNonneg (show 0 ≤ s - 1 by omega)
      nlinarith
  have bounded := quadratic_le_of_endpoints d (-2 * m * s) (-previous * s * s)
    1 (a * s - 1) r (-2) dPositive.le (by omega) interval atLo atHi
  nlinarith

def previousDenominator (n : Nat) : Nat → Int
  | 0 => n
  | index + 1 => (trajectory n index).2

theorem previous_product (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    (trajectory n index).2 * previousDenominator n index =
      (n : Int) - (trajectory n index).1 ^ 2 := by
  cases index with
  | zero => simp [trajectory, previousDenominator]
  | succ index =>
      simpa only [previousDenominator, mul_comm] using trajectory_product n index nonsquare

theorem trajectory_bounds (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    0 ≤ (trajectory n index).1 ∧ (trajectory n index).1 ≤ Nat.sqrt n ∧
    (trajectory n index).2 ≤ Nat.sqrt n + (trajectory n index).1 ∧
    1 ≤ coefficient (Nat.sqrt n) (trajectory n index) := by
  cases index with
  | zero =>
      have root := (sqrt_bounds n nonsquare).root_positive
      simpa [trajectory, coefficient] using
        (show (0 : Int) ≤ 0 ∧ 0 ≤ Nat.sqrt n ∧ 1 ≤ (Nat.sqrt n : Int) ∧
          1 ≤ (Nat.sqrt n : Int) by omega)
  | succ index =>
      have valid := trajectory_reduced n (index + 1) (by omega) nonsquare
      exact ⟨valid.1, valid.2.1, valid.2.2.2.2.1, coefficient_positive valid⟩

theorem denominator_lower (n root m d previous : Int) (below : root * root < n)
    (mUpper : m ≤ root) (dPositive : 0 < d) (dUpper : d ≤ root + m)
    (product : d * previous = n - m * m) : root - m < previous := by
  by_contra absent
  have upper : previous ≤ root - m := by omega
  have scaled := mul_le_mul_of_nonneg_left upper dPositive.le
  have further := mul_le_mul_of_nonneg_left dUpper (show 0 ≤ root - m by omega)
  nlinarith

theorem state_remainder_nonnegative (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (r s : Int) (rPositive : 0 < r) (sPositive : 0 < s)
    (normLower : -1 ≤ (trajectory n index).2 * r * r -
      2 * (trajectory n index).1 * r * s - previousDenominator n index * s * s) :
    0 ≤ r - coefficient (Nat.sqrt n) (trajectory n index) * s := by
  let root : Int := Nat.sqrt n
  let m := (trajectory n index).1
  let d := (trajectory n index).2
  let previous := previousDenominator n index
  let a := coefficient root (trajectory n index)
  let nextM := (trajectory n (index + 1)).1
  let nextD := (trajectory n (index + 1)).2
  have current := trajectory_bounds n index nonsquare
  have next := trajectory_bounds n (index + 1) nonsquare
  have dPositive : 0 < d := trajectory_denominator_positive n index nonsquare
  have offset : d * a = m + nextM := by
    have step := congrArg Prod.fst (trajectory_step n index)
    change d * a - m = nextM at step
    omega
  have dNextUpper : d ≤ root + nextM := by
    have scaled := mul_le_mul_of_nonneg_left current.2.2.2 dPositive.le
    change d * 1 ≤ d * a at scaled
    rw [offset] at scaled
    have mUpper : m ≤ root := current.2.1
    omega
  have product : d * previous = (n : Int) - m * m := by
    simpa only [pow_two] using previous_product n index nonsquare
  have nextProduct : d * nextD = (n : Int) - nextM * nextM := by
    simpa only [pow_two] using trajectory_product n index nonsquare
  have below : root * root < (n : Int) := by
    simpa only [pow_two] using (sqrt_bounds n nonsquare).below
  have previousLower := denominator_lower n root m d previous below current.2.1
    dPositive current.2.2.1 product
  have nextLower := denominator_lower n root nextM d nextD below next.2.1
    dPositive dNextUpper nextProduct
  have recurrence : previous = d * a * a - 2 * m * a + nextD := by
    apply mul_left_cancel₀ (ne_of_gt dPositive)
    calc
      d * previous = (n : Int) - m * m := product
      _ = (d * a - m) ^ 2 + d * nextD - m * m := by
        rw [show d * a - m = nextM by omega, nextProduct]
        ring
      _ = d * (d * a * a - 2 * m * a + nextD) := by ring
  exact remainder_nonnegative root m d previous a nextM nextD r s current.1 current.2.1
    dPositive current.2.2.1 previousLower current.2.2.2 next.1 next.2.1 nextLower
    dNextUpper offset recurrence rPositive sPositive normLower

def Represents (values : Convergents) (x y r s : Int) : Prop :=
  x = values.currentP * r + values.olderP * s ∧
    y = values.currentQ * r + values.olderQ * s

theorem represents_advance (values : Convergents) (a x y r s : Int)
    (represented : Represents values x y r s) :
    Represents (advance a values) x y s (r - a * s) := by
  constructor
  · calc
      x = values.currentP * r + values.olderP * s := represented.1
      _ = (advance a values).currentP * s + (advance a values).olderP * (r - a * s) := by
        dsimp [advance]
        ring
  · calc
      y = values.currentQ * r + values.olderQ * s := represented.2
      _ = (advance a values).currentQ * s + (advance a values).olderQ * (r - a * s) := by
        dsimp [advance]
        ring

theorem older_norm (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    norm n (convergents n index).olderP (convergents n index).olderQ =
      -((-1 : Int) ^ index) * previousDenominator n index := by
  have valid := convergents_invariant n index nonsquare
  apply mul_left_cancel₀ (ne_of_gt (trajectory_denominator_positive n index nonsquare))
  calc
    (trajectory n index).2 * norm n (convergents n index).olderP
        (convergents n index).olderQ =
      (-1 : Int) ^ index * ((trajectory n index).1 * (trajectory n index).1 - n) := valid.older
    _ = -((-1 : Int) ^ index) * ((n : Int) - (trajectory n index).1 ^ 2) := by ring
    _ = (trajectory n index).2 * (-((-1 : Int) ^ index) * previousDenominator n index) := by
      rw [← previous_product n index nonsquare]
      ring

theorem norm_combination (n r s : Int) (values : Convergents) :
    norm n (values.currentP * r + values.olderP * s)
      (values.currentQ * r + values.olderQ * s) =
      r * r * norm n values.currentP values.currentQ + 2 * r * s * mixed n values +
        s * s * norm n values.olderP values.olderQ := by
  dsimp [norm, mixed]
  ring

theorem represented_norm (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (x y r s : Int) (represented : Represents (convergents n index) x y r s) :
    norm n x y = (-1 : Int) ^ index * ((trajectory n index).2 * r * r -
      2 * (trajectory n index).1 * r * s - previousDenominator n index * s * s) := by
  have valid := convergents_invariant n index nonsquare
  rw [represented.1, represented.2, norm_combination, valid.current, valid.cross,
    older_norm n index nonsquare]
  ring

theorem sign_squared (index : Nat) : ((-1 : Int) ^ index) * ((-1 : Int) ^ index) = 1 := by
  rw [← pow_add, show index + index = 2 * index by omega, pow_mul]
  simp

theorem represented_norm_one (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (x y r s : Int) (represented : Represents (convergents n index) x y r s)
    (pell : norm n x y = 1) :
    (trajectory n index).2 * r * r - 2 * (trajectory n index).1 * r * s -
      previousDenominator n index * s * s = (-1 : Int) ^ index := by
  have equation := represented_norm n index nonsquare x y r s represented
  rw [pell] at equation
  calc
    _ = (((-1 : Int) ^ index) * ((-1 : Int) ^ index)) *
        ((trajectory n index).2 * r * r - 2 * (trajectory n index).1 * r * s -
          previousDenominator n index * s * s) := by rw [sign_squared, one_mul]
    _ = ((-1 : Int) ^ index) * 1 := by rw [mul_assoc, ← equation]
    _ = (-1 : Int) ^ index := by ring

/-- The remainder sum strictly decreases until the given Pell solution is a convergent. -/
theorem solution_descent (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (x y r s : Int) (yPositive : 0 < y) (pell : norm n x y = 1)
    (rPositive : 0 < r) (sNonneg : 0 ≤ s)
    (represented : Represents (convergents n index) x y r s) :
    ∃ hit : Nat, 0 < hit ∧ norm n (convergents n hit).currentP (convergents n hit).currentQ = 1 ∧
      (convergents n hit).currentP = x := by
  by_cases zero : s = 0
  · have multiplied : r * r * norm n (convergents n index).currentP
        (convergents n index).currentQ = 1 := by
      calc
        _ = norm n x y := by
          rw [represented.1, represented.2, zero]
          dsimp [norm]
          ring
        _ = 1 := pell
    have normPositive : 0 < norm n (convergents n index).currentP
        (convergents n index).currentQ := by
      by_contra absent
      have nonpos := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg rPositive.le rPositive.le)
        (show norm n (convergents n index).currentP (convergents n index).currentQ ≤ 0 by omega)
      omega
    have scaled := mul_le_mul_of_nonneg_left (show 1 ≤ norm n (convergents n index).currentP
      (convergents n index).currentQ by omega) (mul_nonneg rPositive.le rPositive.le)
    have one : r = 1 := by nlinarith
    have sameX : x = (convergents n index).currentP := by
      simpa only [zero, one, mul_one, mul_zero, add_zero] using represented.1
    have sameY : y = (convergents n index).currentQ := by
      simpa only [zero, one, mul_one, mul_zero, add_zero] using represented.2
    refine ⟨index, ?_, ?_, sameX.symm⟩
    · by_contra absent
      have indexZero : index = 0 := by omega
      rw [indexZero] at sameY
      simp [convergents, initial] at sameY
      omega
    · rw [← sameX, ← sameY]
      exact pell
  · have sPositive : 0 < s := by omega
    have normLower : -1 ≤ (trajectory n index).2 * r * r -
        2 * (trajectory n index).1 * r * s - previousDenominator n index * s * s := by
      rw [represented_norm_one n index nonsquare x y r s represented pell]
      have square := sign_squared index
      nlinarith
    have nextNonneg := state_remainder_nonnegative n index nonsquare r s
      rPositive sPositive normLower
    have next := represents_advance (convergents n index)
      (coefficient (Nat.sqrt n) (trajectory n index)) x y r s represented
    exact solution_descent n (index + 1) nonsquare x y s
      (r - coefficient (Nat.sqrt n) (trajectory n index) * s) yPositive pell sPositive nextNonneg
      (by simpa only [convergents] using next)
termination_by (r + s).toNat
decreasing_by
  have aPositive := (trajectory_bounds n index nonsquare).2.2.2
  have scaled := mul_le_mul_of_nonneg_right aPositive sNonneg
  simp only [one_mul] at scaled
  omega

theorem solution_appears (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (x y : Int) (xPositive : 0 < x) (yPositive : 0 < y) (pell : norm n x y = 1) :
    ∃ index : Nat, 0 < index ∧
      norm n (convergents n index).currentP (convergents n index).currentQ = 1 ∧
      (convergents n index).currentP = x := by
  exact solution_descent n 0 nonsquare x y x y yPositive pell xPositive yPositive.le
    (by constructor <;> simp [convergents, initial])

theorem currentP_mono (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    Monotone (fun index => (convergents n index).currentP) := by
  apply monotone_nat_of_le_succ
  intro index
  cases index with
  | zero =>
      have root := (sqrt_bounds n nonsquare).root_positive
      simpa [convergents, advance, initial, trajectory, coefficient] using
        (show (1 : Int) ≤ Nat.sqrt n by omega)
  | succ index =>
      have positive := convergents_positive n (index + 1) nonsquare (by omega)
      have aPositive := (trajectory_bounds n (index + 1) nonsquare).2.2.2
      have scaled := mul_le_mul_of_nonneg_right aPositive positive.2.1.le
      change (convergents n (index + 1)).currentP ≤
        coefficient (Nat.sqrt n) (trajectory n (index + 1)) *
          (convergents n (index + 1)).currentP + (convergents n (index + 1)).olderP
      nlinarith [positive.1]

/-- The first norm-one convergent is the least positive Pell solution. -/
theorem firstHit_minimum (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    (convergents n (firstHit n nonsquare)).currentP = PellMinimum.minimum n := by
  have xPositive : (0 : Int) < PellMinimum.minimum n := by
    exact_mod_cast (show 0 < PellMinimum.minimum n by
      have := PellMinimum.minimum_positive n nonsquare
      omega)
  have yPositive : (0 : Int) < PellMinimum.firstY n nonsquare := by
    exact_mod_cast (show 0 < PellMinimum.firstY n nonsquare by
      have := (PellMinimum.firstY_qualifies n nonsquare).1
      omega)
  have pell : norm n (PellMinimum.minimum n) (PellMinimum.firstY n nonsquare) = 1 := by
    have equation : (PellMinimum.minimum n : Int) * PellMinimum.minimum n =
        (n : Int) * PellMinimum.firstY n nonsquare * PellMinimum.firstY n nonsquare + 1 := by
      exact_mod_cast PellMinimum.minimum_solution n nonsquare
    dsimp [norm]
    omega
  obtain ⟨index, positive, hit, same⟩ := solution_appears n nonsquare
    (PellMinimum.minimum n) (PellMinimum.firstY n nonsquare) xPositive yPositive pell
  have first : firstHit n nonsquare ≤ index :=
    Nat.find_min' (exists_hit n nonsquare) ⟨positive, hit⟩
  exact le_antisymm (by simpa only [same] using currentP_mono n nonsquare first)
    (minimum_le_firstHit n nonsquare)

end ProjectEulerStatements.PellConvergents
