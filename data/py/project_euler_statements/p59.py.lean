import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p59.py.ast»
import lang.py.FormalSW.Calls

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p59
open FormalSW.PyAst
private abbrev program := P59Ast.module

/-- The source XOR helper terminates for both positive and negative integers. -/
theorem xor.result (a b : Int) :
    Calls.ReturnsValue program "xor" [.int a, .int b] (.int (integerBitXor a b)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.binary (Calls.Evaluates.lookup rfl) (Calls.Evaluates.lookup rfl) rfl

theorem xor.«Returns» (a b : Int) :
    (Calls.function program "xor" [.int a, .int b]).Returns :=
  (xor.result a b).returns

end data.«project-euler-statements».data.py.project_euler_statements.p59
