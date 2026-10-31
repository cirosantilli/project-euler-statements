import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p86.py.ast»
import ProjectEulerSolutions.Lib.CuboidRoute
import lang.py.FormalSW.Calls

namespace data.«project-euler-statements».data.py.project_euler_statements.p86
open FormalSW.PyAst Calls ProjectEulerSolutions.CuboidRoute
set_option Elab.async false

abbrev program := P86Ast.module

/-- The reference's square test agrees with the exact arithmetic predicate. -/
theorem is_square.result (n : Nat) :
    ReturnsValue program "is_square" [.int n] (.bool (decide (square n))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .int (Nat.sqrt n))
  · apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
    change some (Math.isqrtCall [.int n]) = _
    have root : Math.isqrt n = Nat.sqrt n := Nat.eq_sqrt.mpr (Math.isqrt_spec n)
    simp [Math.isqrtCall, root, show ¬(n : Int) < 0 by omega]
  apply BlockReturns.return_value
  apply Evaluates.compare (av := .int (Nat.sqrt n * Nat.sqrt n : Nat)) (bv := .int n)
  · exact Evaluates.binary (av := .int (Nat.sqrt n)) (bv := .int (Nat.sqrt n))
      (Evaluates.lookup (by simp [ScalarEnv.set]))
      (Evaluates.lookup (by simp [ScalarEnv.set])) (by simp [scalarBinary])
  · exact Evaluates.lookup rfl
  · simp [scalarCompare, evalCmpOp, square]
    norm_cast

end data.«project-euler-statements».data.py.project_euler_statements.p86
