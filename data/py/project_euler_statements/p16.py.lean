import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p16.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P16

namespace data.«project-euler-statements».data.py.project_euler_statements.p16
open FormalSW.PyAst
private abbrev program := P16Ast.module

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 3 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digit_sum", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private abbrev digits (n : Nat) : List Mutable.Value :=
  (Nat.digits 10 n).map (fun (d : Nat) => .scalar (.int (d : Int)))

theorem digit_sum.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "digit_sum" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P16.digitSum n))) (heap ++ [.list (digits n)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  have converted := (common.digits_le.decimal n heap).extend common_extension
  have total : ((Nat.digits 10 n).map (fun (d : Nat) => (d : Int))).foldl Int.add 0 =
      ((Nat.digits 10 n).sum : Int) := by
    calc
      _ = ((Nat.digits 10 n).map (fun (d : Nat) => (d : Int))).sum := List.sum_eq_foldl.symm
      _ = _ := by simp
  change HeapCalls.Evaluates program _ _ heap (.scalar (.int ((Nat.digits 10 n).sum : Int))) _
  rw [← total]
  apply HeapCalls.Evaluates.sum_integers (initial := 0)
    (values := (Nat.digits 10 n).map (fun (d : Nat) => (d : Int)))
  · exact .cons (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) converted)
      (.cons HeapCalls.Evaluates.constant .nil)
  · simp [Mutable.sequence, digits, List.map_map, Function.comp_def]

theorem naive.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "naive" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P16.naive n))) (heap ++ [.list (digits (2 ^ n))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.binary (finalHeap := heap)
    (value := .scalar (.int ((2 ^ n : Nat) : Int))) HeapCalls.Evaluates.constant
    (HeapCalls.Evaluates.lookup rfl) (by simp [Mutable.binary, scalarBinary, show ¬(n : Int) < 0 by omega])) .nil)
  exact digit_sum.result (2 ^ n) heap

theorem naive.«Returns» (n : Int)
    (condition : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      P16Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  exact (naive.result n []).scalar_returns

theorem naive.«Supported» (n : Int)
    (condition : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      P16Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int n]).Supported :=
  (naive.«Returns» n condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p16
