import data.«project-euler-statements».data.py.project_euler_statements.«p91.py.lean.d».Loops

namespace data.«project-euler-statements».data.py.project_euler_statements.p91.naive
open FormalSW.PyAst Calls ProjectEulerSolutions.LatticeRightTriangles
set_option Elab.async false

theorem natural_result (n : Nat) :
    ReturnsValue program "naive" [number n] (number (referenceCount n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := number 0) Evaluates.constant
  apply BlockReturns.for_range (values := [number (n + 1)])
  · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarBinary, number])) .nil
  · rfl
  apply grid_result n 0 0 _ rfl rfl
  intro after _ getTotal
  apply BlockReturns.return_value
  apply Evaluates.binary (Evaluates.lookup getTotal) Evaluates.constant
  simp [scalarBinary, number, referenceCount, gridSum, cubeSum, planeSum, rowSum,
    weight, ← Nat.range_succ_eq_Icc_zero, Int.natCast_ediv]

/-- Negative bounds execute an empty outer range; nonnegative bounds traverse the whole grid. -/
theorem result (n : Int) :
    ReturnsValue program "naive" [.int n] (number (optimizedCount n.toNat)) := by
  by_cases nonnegative : 0 ≤ n
  · have cast : (n.toNat : Int) = n := Int.toNat_of_nonneg nonnegative
    simpa only [number, cast, referenceCount_eq] using natural_result n.toNat
  · have zero : n.toNat = 0 := by omega
    have count : optimizedCount n.toNat = 0 := by simp [zero, optimizedCount, pointContribution]
    rw [count]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (value := number 0) Evaluates.constant
    apply BlockReturns.for_range (values := [.int (n + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
        (by simp [scalarBinary])) .nil
    · rfl
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply BlockReturns.return_value
    exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl

end data.«project-euler-statements».data.py.project_euler_statements.p91.naive
