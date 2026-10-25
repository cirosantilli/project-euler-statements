import data.«project-euler-statements».data.py.project_euler_statements.«p61.polygonal.source»
import ProjectEulerSolutions.Lib.PolygonalCycleSearch
import lang.py.FormalSW.SumCalls

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p61
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions

private abbrev program := P61Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

theorem last_two.heap_result (value : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "last_two" [number value] heap (number (value % 100)) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
    (av := number value) (bv := number 100) (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
  simp [Mutable.binary, scalarBinary, number]

theorem first_two.heap_result (value : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "first_two" [number value] heap (number (value / 100)) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
    (av := number value) (bv := number 100) (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
  simp [Mutable.binary, scalarBinary, number]

theorem is_cyclic_pair.heap_result (left right : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "is_cyclic_pair" [number left, number right] heap
      (flag (ProjectEulerSolutions.PolygonalCycle.links left right)) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (middle := heap) (afterRight := heap) (finalHeap := heap)
    (av := number (left % 100)) (bv := number (right / 100))
  · exact Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (last_two.heap_result left heap globals)
  · exact Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (first_two.heap_result right heap globals)
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp, ProjectEulerSolutions.PolygonalCycle.links, flag]

namespace extend
private def numbers (values : List Int) : List Mutable.Value := values.map number
private def exhausted : Expr := .unaryOp .not (.name "remaining")
private def closes : Expr := .call (.name "is_cyclic_pair")
  [.subscript (.name "path") (.unaryOp .uSub (.constant (.int 1))),
   .subscript (.name "path") (.constant (.int 0))]
private def sumPath : Expr := .sumSequence (.name "path") (.constant (.int 0))
private def baseBody : List Stmt := [.ifThen closes [.return sumPath] [], .return (.constant (.int 0))]

theorem base_source :
    (executableBody ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).2)[0]? =
      some (.ifThen exhausted baseBody []) := rfl

/-- Exhausting the type list tests the actual endpoints and returns the actual path sum. -/
theorem closed_result (values : List Int) (nonempty : values ≠ []) (heap : Mutable.Heap) (path remaining : Nat)
    (pathFound : heap[path]? = some (.list (numbers values)))
    (remainingFound : heap[remaining]? = some (.list [])) (familiesCell : Mutable.Value)
    (globals : Mutable.Globals := []) :
    ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remaining, familiesCell] heap
      (number (if ProjectEulerSolutions.PolygonalCycleSearch.closed values then values.sum else 0)) heap globals := by
  have positive : 0 < values.length := List.length_pos_iff.mpr nonempty
  let first := values[0]'positive
  let last := values[values.length - 1]'(by omega)
  have head : values[0]? = some first := List.getElem?_eq_getElem positive
  have tail : values[values.length - 1]? = some last := List.getElem?_eq_getElem (by omega)
  have closed : ProjectEulerSolutions.PolygonalCycleSearch.closed values =
      ProjectEulerSolutions.PolygonalCycle.links last first := by
    simp [ProjectEulerSolutions.PolygonalCycleSearch.closed, ProjectEulerSolutions.PolygonalCycle.links, List.head?_eq_getElem?, List.getLast?_eq_getElem?, head, tail]
  let params := ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).2
  let env := functionEnv params sourceBody [.ref path, .ref remaining, familiesCell] globals
  have getPath : env "path" = some (.ref path) := by cases globals <;> rfl
  have getRemaining : env "remaining" = some (.ref remaining) := by cases globals <;> rfl
  have done : Evaluates program env exhausted heap (flag true) heap globals := by
    apply Evaluates.unary (middle := heap) (finalHeap := heap) (Evaluates.lookup getRemaining)
    simp [HeapCalls.unary, Mutable.truth, remainingFound, flag]
  have firstRun : Evaluates program env (.subscript (.name "path") (.constant (.int 0))) heap
      (number first) heap globals := by
    apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getPath) Evaluates.constant
    have got := Mutable.getItem_list heap path 0 (numbers values) pathFound (by simp [numbers]; omega)
    simpa [numbers, first] using got
  have lastRun : Evaluates program env (.subscript (.name "path") (.unaryOp .uSub (.constant (.int 1)))) heap
      (number last) heap globals := by
    apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getPath)
      (Evaluates.unary (middle := heap) (finalHeap := heap) (value := number 1) Evaluates.constant rfl)
    have offset : ((-1 : Int) + values.length).toNat = values.length - 1 := by omega
    have indexed : Mutable.index (numbers values) (number (-1)) heap = some (.ok (values.length - 1), heap) := by
      simp [Mutable.index, numbers, nonempty, offset]
    have mapped : (numbers values)[values.length - 1]? = some (number last) := by simp [numbers, tail]
    simp [Mutable.getItem, pathFound, indexed, Except.map, mapped]
  have tested : Evaluates program env closes heap (flag (ProjectEulerSolutions.PolygonalCycleSearch.closed values)) heap globals := by
    rw [closed]
    exact Evaluates.call (.cons lastRun (.cons firstRun .nil)) (is_cyclic_pair.heap_result last first heap globals)
  have summed : Evaluates program env sumPath heap (number values.sum) heap globals := by
    have evaluated := Evaluates.sum_integers (module := program) (globals := globals)
      (heap := heap) (middle := heap) (initial := 0) (values := values)
      (.cons (Evaluates.lookup getPath) (.cons Evaluates.constant .nil))
      (by simp [Mutable.sequence, pathFound, numbers])
    have total : values.sum = values.foldl Int.add 0 := List.sum_eq_foldl
    rw [← total] at evaluated
    exact evaluated
  apply BlockReturns.function rfl rfl
  change BlockReturns program env (.ifThen exhausted baseBody [] :: (executableBody sourceBody).drop 1) heap _ heap globals
  apply BlockReturns.branch (flag := true) done rfl
  cases selected : ProjectEulerSolutions.PolygonalCycleSearch.closed values with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply BlockReturns.branch (flag := false) (by simpa only [selected] using tested) rfl
      exact BlockReturns.return_value Evaluates.constant
  | true =>
      simp only [if_true]
      apply BlockReturns.branch (flag := true) (by simpa only [selected] using tested) rfl
      exact BlockReturns.return_value summed

end extend
end data.«project-euler-statements».data.py.project_euler_statements.p61
