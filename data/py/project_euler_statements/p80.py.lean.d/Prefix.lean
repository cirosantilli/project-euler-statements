import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p80.py.ast»
import ProjectEulerSolutions.Lib.SquareRootDigitCalls
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»

namespace data.«project-euler-statements».data.py.project_euler_statements.p80
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.SquareRootDigitCalls
set_option Elab.async false
private abbrev program := P80Ast.module
private abbrev digits (n : Nat) := (Nat.digits 10 n).map number

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digit_sum", "is_square", "sqrt_digits_sum", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem digit_sum.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "digit_sum" [number n] heap (number (Nat.digits 10 n).sum)
      (heap ++ [.list (digits n)]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have converted := (common.digits_le.decimal n heap globals).extend common_extension
  have total : ((Nat.digits 10 n).map (fun d : Nat => (d : Int))).foldl Int.add 0 =
      ((Nat.digits 10 n).sum : Int) := by
    have folded := List.foldl_map_hom (g := fun d : Nat => (d : Int))
      (f := Nat.add) (f' := Int.add) (a := 0) (l := (Nat.digits 10 n))
      (by intro a b; exact (Nat.cast_add a b).symm)
    exact folded.trans (congrArg (fun value : Nat => (value : Int))
      (List.sum_eq_foldl_nat (xs := Nat.digits 10 n)).symm)
  change Evaluates program _ _ heap (.scalar (.int ((Nat.digits 10 n).sum : Int))) _ globals
  rw [← total]
  apply Evaluates.sum_integers (initial := 0) (values := (Nat.digits 10 n).map (fun d : Nat => (d : Int)))
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) converted)
      (.cons Evaluates.constant .nil)
  · simp [Mutable.sequence, digits, List.map_map, Function.comp_def]

theorem is_square.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "is_square" [number n] heap
      (.scalar (.bool (decide (Nat.sqrt n * Nat.sqrt n = n)))) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := number (Nat.sqrt n))
    (isqrt_call n (.name "n") (Evaluates.lookup (by cases globals <;> rfl)) rfl rfl)
  apply BlockReturns.return_value
  apply Evaluates.compare (av := number (Nat.sqrt n * Nat.sqrt n)) (bv := number n) (middle := heap) (afterRight := heap)
  · exact Evaluates.binary (av := number (Nat.sqrt n)) (bv := number (Nat.sqrt n)) (middle := heap) (afterRight := heap) (finalHeap := heap) (Evaluates.lookup (by simp [setLocal])) (Evaluates.lookup (by simp [setLocal]))
      (by simp [Mutable.binary, scalarBinary, number])
  · exact Evaluates.lookup (by cases globals <;> rfl)
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    norm_cast

theorem sqrt_digits_sum.result (n precision : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "sqrt_digits_sum" [number n, number precision] heap
      (number (ProjectEulerStatements.P80.sqrtDigitsSum n precision)) (heap ++ extra) globals := by
  by_cases square : Nat.sqrt n * Nat.sqrt n = n
  · refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (value := .scalar (.bool true))
    · simpa only [square, decide_true] using
        (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (is_square.result n heap globals))
    · rfl
    · simpa [ProjectEulerStatements.P80.sqrtDigitsSum, ProjectEulerStatements.P80.isSquare, square] using
        (BlockReturns.return_value (module := program) (env := _) (rest := _) (globals := globals)
          (heap := heap) (Evaluates.constant (value := .int 0)))
  · refine ⟨[.list (digits (ProjectEulerStatements.P80.sqrtPrefix n precision))], ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (value := .scalar (.bool false))
    · simpa only [square, decide_false] using
        (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (is_square.result n heap globals))
    · rfl
    · apply BlockReturns.assign (value := number (Nat.sqrt n))
        (isqrt_call n (.name "n") (Evaluates.lookup (by cases globals <;> rfl)) rfl rfl)
      apply BlockReturns.assign (value := number (ProjectEulerStatements.P80.integerWidth n))
        (width_evaluate n (by simp [setLocal]))
      apply (prefix_result n precision (by cases globals <;> rfl) (by cases globals <;> rfl)
        (by simp [setLocal]) (by simp [setLocal]) (by rfl) (by rfl)).returns
      apply BlockReturns.return_value
      simpa [ProjectEulerStatements.P80.sqrtDigitsSum, ProjectEulerStatements.P80.isSquare,
        square, ProjectEulerStatements.P80.digitSum] using
        (Evaluates.call (.cons (Evaluates.lookup (by simp [setLocal])) .nil)
          (digit_sum.result (ProjectEulerStatements.P80.sqrtPrefix n precision) heap globals))

end data.«project-euler-statements».data.py.project_euler_statements.p80
