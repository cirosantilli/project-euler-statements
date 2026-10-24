import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p20.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P20
import ProjectEulerStatements.Lib.Factorial

namespace data.«project-euler-statements».data.py.project_euler_statements.p20
open FormalSW.PyAst
private abbrev program := P20Ast.module

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
      (.scalar (.int (ProjectEulerStatements.P20.digitSum n))) (heap ++ [.list (digits n)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  have converted := (common.digits_le.decimal n heap).extend common_extension
  have total : ((Nat.digits 10 n).map (fun (d : Nat) => (d : Int))).foldl Int.add 0 =
      ((Nat.digits 10 n).sum : Int) := by
    have folded := List.foldl_map_hom (g := fun d : Nat => (d : Int))
      (f := Nat.add) (f' := Int.add) (a := 0) (l := (Nat.digits 10 n))
      (by intro a b; exact (Nat.cast_add a b).symm)
    exact folded.trans (congrArg (fun value : Nat => (value : Int))
      (List.sum_eq_foldl_nat (xs := (Nat.digits 10 n))).symm)
  change HeapCalls.Evaluates program _ _ heap (.scalar (.int ((Nat.digits 10 n).sum : Int))) _
  rw [← total]
  apply HeapCalls.Evaluates.sum_integers (initial := 0)
    (values := (Nat.digits 10 n).map (fun (d : Nat) => (d : Int)))
  · exact .cons (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) converted)
      (.cons HeapCalls.Evaluates.constant .nil)
  · simp [Mutable.sequence, digits, List.map_map, Function.comp_def]

theorem factorial_eq (n : Nat) : Math.factorial n = Nat.factorial n :=
  ProjectEulerStatements.Factorial.recurrence_eq Math.factorial rfl (fun _ => rfl) n

theorem naive.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "naive" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P20.naive n)))
      (heap ++ [.list (digits (Nat.factorial n))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.call (middle := heap) (values := [.scalar (.int (Nat.factorial n))])
  · refine .cons ?_ .nil
    apply HeapCalls.Evaluates.library_call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) rfl
    change some (Except.map Mutable.Value.scalar (Math.factorialCall [.int n]), heap) = _
    rw [Math.factorialCall_natural, factorial_eq]
    rfl
  · exact digit_sum.result (Nat.factorial n) heap

theorem naive.«Returns» (n : Int)
    (condition : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      P20Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  exact (naive.result n []).scalar_returns

theorem naive.«Supported» (n : Int)
    (condition : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      P20Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int n]).Supported :=
  (naive.«Returns» n condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p20
