import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p58.py.ast»
import FormalSW

namespace data.«project-euler-statements».data.py.project_euler_statements.p58
open FormalSW.PyAst FormalSW.PyAst.Calls
set_option Elab.async false

private abbrev program := P58Ast.module

/-- The actual source computes the diagonal total as an integer polynomial, including signed inputs. -/
theorem diag_total.result (k : Int) :
    ReturnsValue program "diag_total" [.int k] (.int (4 * k + 1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .int (2 * k + 1))
  · exact Evaluates.binary
      (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant rfl
  · apply BlockReturns.return_value
    apply Evaluates.binary
      (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant
    simp [scalarBinary]
    omega

theorem diag_total.«Returns» (k : Int) :
    (FormalSW.PyAst.scalarFunction program "diag_total" [.int k]).Returns :=
  ⟨.int (2 * (2 * k + 1) - 1), .next rfl (.done rfl)⟩

/-- The same source helper leaves both heap and cache unchanged inside the reference scan. -/
theorem diag_total.memo_result (k : Int) (heap : Mutable.Heap) (spec : HeapMemoCalls.Specification) :
    HeapMemoCalls.ReturnsRel program spec "diag_total" [.scalar (.int k)] heap
      (fun value after => value = .scalar (.int (4 * k + 1)) ∧ after = heap) := by
  apply HeapMemoCalls.BlockReturnsRel.function (by decide) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.assign
    (HeapMemoCalls.Evaluates.binary (value := .scalar (.int (2 * k + 1)))
      (HeapMemoCalls.Evaluates.binary HeapMemoCalls.Evaluates.constant
        (HeapMemoCalls.Evaluates.lookup rfl) rfl) HeapMemoCalls.Evaluates.constant rfl).rel
  rintro value middle ⟨rfl, rfl⟩
  apply HeapMemoCalls.BlockReturnsRel.return_value
  apply (HeapMemoCalls.Evaluates.binary (value := .scalar (.int (4 * k + 1)))
    (HeapMemoCalls.Evaluates.binary HeapMemoCalls.Evaluates.constant
      (HeapMemoCalls.Evaluates.lookup rfl) rfl) HeapMemoCalls.Evaluates.constant ?_).rel
  simp [Mutable.binary, scalarBinary]
  omega

end data.«project-euler-statements».data.py.project_euler_statements.p58
