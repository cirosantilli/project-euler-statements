import data.«project-euler-statements».data.py.project_euler_statements.«p91.py.lean.d».Counting

namespace data.«project-euler-statements».data.py.project_euler_statements.p91.naive
open FormalSW.PyAst Calls ProjectEulerSolutions ProjectEulerSolutions.LatticeRightTriangles
open scoped BigOperators
set_option Elab.async false

def planeSum (n a b first : Nat) : Nat := ∑ c ∈ Finset.Icc first n, rowSum n a b c 0
def cubeSum (n a first : Nat) : Nat := ∑ b ∈ Finset.Icc first n, planeSum n a b 0
def gridSum (n first : Nat) : Nat := ∑ a ∈ Finset.Icc first n, cubeSum n a 0

theorem plane_result (n a b c total : Nat) (env : ScalarEnv)
    (getN : env "n" = some (number n))
    (getA : env "x1" = some (number a))
    (getB : env "y1" = some (number b))
    (getTotal : env "acc" = some (number total))
    (following : List Stmt) (answer : Constant)
    (rest : ∀ after, after "n" = some (number n) → after "x1" = some (number a) → after "y1" = some (number b) →
      after "acc" = some (number (total + planeSum n a b c)) →
      BlockReturns program after following answer) :
    BlockReturns program env (.rangeStepLoop "x2" c (n + 1) 1 x2Body [] :: following) answer := by
  by_cases inside : c ≤ n
  · let entered := env.set "x2" (number c)
    have enteredN : entered "n" = some (number n) := by
      simpa [entered, ScalarEnv.set] using getN
    have enteredA : entered "x1" = some (number a) := by
      simpa [entered, ScalarEnv.set] using getA
    have enteredB : entered "y1" = some (number b) := by
      simpa [entered, ScalarEnv.set] using getB
    have enteredTotal : entered "acc" = some (number total) := by
      simpa [entered, ScalarEnv.set] using getTotal
    have enteredIndex : entered "x2" = some (number c) := by simp [entered, ScalarEnv.set]
    have step := NaturalIntervalSum.step (fun c => rowSum n a b c 0) c n inside
    change planeSum n a b c = rowSum n a b c 0 + planeSum n a b (c + 1) at step
    apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    apply BlockReturns.for_range (values := [number (n + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup enteredN) Evaluates.constant
        (by simp [scalarBinary, number])) .nil
    · rfl
    apply row_result n a b c 0 total entered ⟨enteredN, enteredA, enteredB, enteredIndex, enteredTotal⟩
    intro after ready
    have continued := plane_result n a b (c + 1) (total + rowSum n a b c 0) after ready.bound ready.firstX ready.firstY ready.count
      following answer (fun final finalN finalA finalB finalTotal => rest final finalN finalA finalB (by
        simpa only [step, Nat.add_assoc] using finalTotal))
    simpa only [Int.natCast_add, Int.natCast_one] using continued
  · apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply rest env getN getA getB
    have empty := NaturalIntervalSum.empty (fun c => rowSum n a b c 0) c n (by omega)
    simpa only [planeSum, empty, Nat.add_zero] using getTotal
termination_by n + 1 - c
decreasing_by omega

theorem cube_result (n a b total : Nat) (env : ScalarEnv)
    (getN : env "n" = some (number n))
    (getA : env "x1" = some (number a))
    (getTotal : env "acc" = some (number total))
    (following : List Stmt) (answer : Constant)
    (rest : ∀ after, after "n" = some (number n) → after "x1" = some (number a) →
      after "acc" = some (number (total + cubeSum n a b)) →
      BlockReturns program after following answer) :
    BlockReturns program env (.rangeStepLoop "y1" b (n + 1) 1 yBody [] :: following) answer := by
  by_cases inside : b ≤ n
  · let entered := env.set "y1" (number b)
    have enteredN : entered "n" = some (number n) := by
      simpa [entered, ScalarEnv.set] using getN
    have enteredA : entered "x1" = some (number a) := by
      simpa [entered, ScalarEnv.set] using getA
    have enteredTotal : entered "acc" = some (number total) := by
      simpa [entered, ScalarEnv.set] using getTotal
    have enteredIndex : entered "y1" = some (number b) := by simp [entered, ScalarEnv.set]
    have step := NaturalIntervalSum.step (fun b => planeSum n a b 0) b n inside
    change cubeSum n a b = planeSum n a b 0 + cubeSum n a (b + 1) at step
    apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    apply BlockReturns.for_range (values := [number (n + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup enteredN) Evaluates.constant
        (by simp [scalarBinary, number])) .nil
    · rfl
    apply plane_result n a b 0 total entered enteredN enteredA enteredIndex enteredTotal
    intro after afterN afterA afterIndex afterTotal
    have continued := cube_result n a (b + 1) (total + planeSum n a b 0) after afterN afterA afterTotal
      following answer (fun final finalN finalA finalTotal => rest final finalN finalA (by
        simpa only [step, Nat.add_assoc] using finalTotal))
    simpa only [Int.natCast_add, Int.natCast_one] using continued
  · apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply rest env getN getA
    have empty := NaturalIntervalSum.empty (fun b => planeSum n a b 0) b n (by omega)
    simpa only [cubeSum, empty, Nat.add_zero] using getTotal
termination_by n + 1 - b
decreasing_by omega

theorem grid_result (n a total : Nat) (env : ScalarEnv)
    (getN : env "n" = some (number n))
    (getTotal : env "acc" = some (number total))
    (following : List Stmt) (answer : Constant)
    (rest : ∀ after, after "n" = some (number n) →
      after "acc" = some (number (total + gridSum n a)) →
      BlockReturns program after following answer) :
    BlockReturns program env (.rangeStepLoop "x1" a (n + 1) 1 xBody [] :: following) answer := by
  by_cases inside : a ≤ n
  · let entered := env.set "x1" (number a)
    have enteredN : entered "n" = some (number n) := by
      simpa [entered, ScalarEnv.set] using getN
    have enteredTotal : entered "acc" = some (number total) := by
      simpa [entered, ScalarEnv.set] using getTotal
    have enteredIndex : entered "x1" = some (number a) := by simp [entered, ScalarEnv.set]
    have step := NaturalIntervalSum.step (fun a => cubeSum n a 0) a n inside
    change gridSum n a = cubeSum n a 0 + gridSum n (a + 1) at step
    apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    apply BlockReturns.for_range (values := [number (n + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup enteredN) Evaluates.constant
        (by simp [scalarBinary, number])) .nil
    · rfl
    apply cube_result n a 0 total entered enteredN enteredIndex enteredTotal
    intro after afterN afterIndex afterTotal
    have continued := grid_result n (a + 1) (total + cubeSum n a 0) after afterN afterTotal
      following answer (fun final finalN finalTotal => rest final finalN (by
        simpa only [step, Nat.add_assoc] using finalTotal))
    simpa only [Int.natCast_add, Int.natCast_one] using continued
  · apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply rest env getN
    have empty := NaturalIntervalSum.empty (fun a => cubeSum n a 0) a n (by omega)
    simpa only [gridSum, empty, Nat.add_zero] using getTotal
termination_by n + 1 - a
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p91.naive
