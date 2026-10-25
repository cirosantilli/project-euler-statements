import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p61.py.ast»
import FormalSW
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ProjectEulerSolutions.Lib.PolygonalCycle
import ProjectEulerSolutions.Lib.HeapCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.polygonal
open FormalSW.PyAst

def answer (sides index : Int) : Int :=
  index * ((sides - 2) * index - (sides - 4)) / 2

def expression (sName nName : String) : Expr :=
  .binOp
    (.binOp (.name nName) .mult
      (.binOp (.binOp (.binOp (.name sName) .sub (.constant (.int 2))) .mult (.name nName))
        .sub (.binOp (.name sName) .sub (.constant (.int 4)))))
    .floorDiv (.constant (.int 2))

private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)

/-- Arithmetic evaluation leaves the caller heap and its global bindings untouched. -/
theorem expression_evaluates (sName nName : String) (s n : Int) (module : Module)
    (env : HeapCalls.Env) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getS : env sName = some (number s)) (getN : env nName = some (number n)) :
    HeapCalls.Evaluates module env (expression sName nName) heap (number (answer s n)) heap globals := by
  apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number (n * ((s - 2) * n - (s - 4)))) (bv := number 2)
  · apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number n) (bv := number ((s - 2) * n - (s - 4)))
    · exact HeapCalls.Evaluates.lookup getN
    · apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number ((s - 2) * n)) (bv := number (s - 4))
      · apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number (s - 2)) (bv := number n)
        · exact HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (HeapCalls.Evaluates.lookup getS)
            HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
        · exact HeapCalls.Evaluates.lookup getN
        · simp [Mutable.binary, scalarBinary, number]
      · exact HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (HeapCalls.Evaluates.lookup getS)
          HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
      · simp [Mutable.binary, scalarBinary, number]
    · simp [Mutable.binary, scalarBinary, number]
  · exact HeapCalls.Evaluates.constant
  · simp [Mutable.binary, scalarBinary, number, answer]

/-- The source helper can be called from a heap-based loop in any caller context. -/
theorem heap_result (s n : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapCalls.ReturnsValue P61Ast.module "polygonal" [number s, number n] heap
      (number (answer s n)) heap globals := by
  let params := ((findFunctionIn P61Ast.module.body "polygonal").getD ([], [])).1
  let body := ((findFunctionIn P61Ast.module.body "polygonal").getD ([], [])).2
  let env := HeapCalls.functionEnv params body [number s, number n] globals
  apply HeapCalls.BlockReturns.function rfl rfl
  change HeapCalls.BlockReturns P61Ast.module env [.return (expression "sides" "index")] heap
    (number (answer s n)) heap globals
  apply HeapCalls.BlockReturns.return_value
  exact expression_evaluates _ _ _ _ _ _ _ _ (by cases globals <;> rfl) (by cases globals <;> rfl)

/-- The actual arithmetic source returns on every pair of signed integers. -/
theorem result (sides index : Int) :
    Finishes (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).step
      (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).initial
      (.ok (.int (answer sides index))) := by
  apply Execution.finishes_of_observe (fuel := 1)
  rfl

theorem «Returns» (sides index : Int) :
    (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).Returns :=
  ⟨.int (answer sides index), result sides index⟩

theorem «Supported» (sides index : Int) :
    (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).Supported :=
  («Returns» sides index).supported

/-- The exact recurrence retains signed floor-division semantics. -/
theorem step (s n : Int) : answer s (n + 1) = answer s n + (s - 2) * n + 1 := by
  unfold answer
  have numerator : (n + 1) * ((s - 2) * (n + 1) - (s - 4)) =
      n * ((s - 2) * n - (s - 4)) + ((s - 2) * n + 1) * 2 := by ring
  rw [numerator, Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0)]
  ring

theorem increasing_step (s n : Int) (sides : 3 ≤ s) (positive : 1 ≤ n) :
    answer s n < answer s (n + 1) := by
  rw [step]
  have product : 0 ≤ (s - 2) * n := mul_nonneg (by omega) (by omega)
  omega

/-- The finite reference window contains every four-digit value of all six families. -/
theorem above_four_digits (s n : Int) (sides : 3 ≤ s) (large : 141 ≤ n) :
    10000 ≤ answer s n := by
  have extra : 0 ≤ (s - 3) * (n * (n - 1)) :=
    mul_nonneg (by omega) (mul_nonneg (by omega) (by omega))
  have triangle : (20000 : Int) ≤ n * (n + 1) := by
    nlinarith [sq_nonneg (n - 141)]
  have numerator : (20000 : Int) ≤ n * ((s - 2) * n - (s - 4)) := by
    nlinarith [extra]
  unfold answer
  omega

end data.«project-euler-statements».data.py.project_euler_statements.p61.polygonal

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

namespace families
private def numbers (values : List Int) : List Mutable.Value := values.map number
private abbrev answer := polygonal.answer

def keep (value : Int) : Bool := decide (1000 ≤ value ∧ value ≤ 9999)
def valueExpression : Expr := .call (.name "polygonal") [.name "sides", .name "n"]
def filterExpression : Expr :=
  .compare (.constant (.int 1000)) [(.ltE, valueExpression), (.lt, .constant (.int 10000))]
def boundExpression : Expr := .binOp (.name "limit") .add (.constant (.int 1))
def familyExpression : Expr :=
  .listComp valueExpression [("n", .call (.name "range") [boundExpression], [filterExpression])]
def expression : Expr :=
  .listComp familyExpression [("sides", .call (.name "range") [.constant (.int 3), .constant (.int 9)], [])]

theorem source :
    (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2)[0]? =
      some (.assign [.name "__formalsw_cell_naive_families"] (.list [expression])) := rfl

theorem value_evaluate (sides index : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getSides : env "sides" = some (number sides)) (getIndex : env "n" = some (number index))
    (globals : Mutable.Globals := []) :
    Evaluates program env valueExpression heap (number (answer sides index)) heap globals :=
  Evaluates.call (.cons (Evaluates.lookup getSides) (.cons (Evaluates.lookup getIndex) .nil))
    (polygonal.heap_result sides index heap globals)

theorem filter_evaluate (sides index : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getSides : env "sides" = some (number sides)) (getIndex : env "n" = some (number index))
    (globals : Mutable.Globals := []) :
    Evaluates program env filterExpression heap (flag (keep (answer sides index))) heap globals := by
  have evaluated := value_evaluate sides index heap env getSides getIndex globals
  apply Evaluates.chain (middle := heap) (value := number 1000) Evaluates.constant
  by_cases lower : 1000 ≤ answer sides index
  · apply Evaluates.Compares.next (compared := flag true) (afterComparison := heap) evaluated
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower, flag]) rfl
    apply Evaluates.Compares.last (middle := heap) (value := number 10000) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, keep, lower, flag]
    omega
  · have rejected : keep (answer sides index) = false := by simp [keep, lower]
    simp only [rejected]
    apply Evaluates.Compares.stop (middle := heap) evaluated
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower, flag]) rfl

private def window (sides : Int) (first count : Nat) : List Int :=
  ((List.range' first count).map (fun index : Nat => answer sides index)).filter keep
private def body (collector : Nat) : List Stmt :=
  [.ifThen filterExpression [.comprehensionAppend collector valueExpression] []]

private theorem family_loop (sides : Int) (base : Mutable.Heap) (before : List Int)
    (first count stop : Nat) (endAt : first + count = stop) (env : HeapCalls.Env)
    (getSides : env "sides" = some (number sides)) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "n" first stop 1 (body base.length) []]
      (HeapCollection.working base (numbers before) []) finalEnv
      (HeapCollection.working base (numbers (before ++ window sides first count)) []) globals := by
  induction count generalizing first before env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [window, List.range'_zero, List.map_nil, List.filter_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "n" (number first)
      have boundSides : bound "sides" = some (number sides) := by simpa [bound, setLocal] using getSides
      have tested := filter_evaluate sides first (HeapCollection.working base (numbers before) []) bound boundSides rfl globals
      cases selected : keep (answer sides first) with
      | false =>
          have skipped : BlockContinues program bound (body base.length)
              (HeapCollection.working base (numbers before) []) bound
              (HeapCollection.working base (numbers before) []) globals :=
            BlockContinues.branch (flag := false) (by simpa only [selected] using tested) rfl .nil
          obtain ⟨finalEnv, continued⟩ := ih before (first + 1) (by omega) bound boundSides
          refine ⟨finalEnv, ?_⟩
          apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
          simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, body, window,
            List.range'_succ, selected] using skipped.append continued
      | true =>
          have emitted : BlockContinues program bound (body base.length)
              (HeapCollection.working base (numbers before) []) bound
              (HeapCollection.working base (numbers (before ++ [answer sides first])) []) globals := by
            apply BlockContinues.branch (flag := true) (by simpa only [selected] using tested) rfl
            have appended := HeapCollection.emit (program := program) base (numbers before) [] [] (number (answer sides first))
              (by simpa only [List.append_nil] using
                value_evaluate sides first (HeapCollection.working base (numbers before) []) bound boundSides rfl globals)
            simpa only [numbers, List.map_append, List.map_cons, List.map_nil, List.append_nil] using appended
          obtain ⟨finalEnv, continued⟩ := ih (before ++ [answer sides first]) (first + 1) (by omega) bound boundSides
          refine ⟨finalEnv, ?_⟩
          apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
          simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, body, window,
            List.range'_succ, selected, List.append_assoc] using emitted.append continued

private theorem map_ints (items : List Nat) (f : Int → Int) :
    items.map (fun item : Nat => f item) = (items : List Int).map f := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      change f head :: rest.map (fun item : Nat => f item) = f head :: (rest : List Int).map f
      exact congrArg (List.cons (f head)) ih

/-- The nested source comprehension scans exactly `range(limit + 1)`, even for negative limits. -/
theorem family_evaluate (sides limit : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getSides : env "sides" = some (number sides)) (getLimit : env "limit" = some (number limit))
    (globals : Mutable.Globals := []) :
    Evaluates program env familyExpression heap (.ref heap.length)
      (heap ++ [.list (numbers (ProjectEulerSolutions.PolygonalCycle.fourDigit limit sides))]) globals := by
  have bound : Evaluates program env boundExpression heap (number (limit + 1)) heap globals := by
    apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup getLimit) Evaluates.constant
    simp [Mutable.binary, scalarBinary, number]
  let masked := comprehensionEnv env [("n", .call (.name "range") [boundExpression], [filterExpression])]
  have maskedSides : masked "sides" = some (number sides) := by
    simpa [masked, comprehensionEnv, setLocal] using getSides
  by_cases positive : 0 < limit + 1
  · obtain ⟨finalEnv, executed⟩ := family_loop sides heap [] 0 (limit + 1).toNat (limit + 1).toNat (by omega) masked maskedSides globals
    have castStop : ((limit + 1).toNat : Int) = limit + 1 := by omega
    rw [castStop] at executed
    have model : window sides 0 (limit + 1).toNat = ProjectEulerSolutions.PolygonalCycle.fourDigit limit sides := by
      unfold window ProjectEulerSolutions.PolygonalCycle.fourDigit
      rw [List.range_eq_range']
      exact congrArg (List.filter keep) (map_ints (List.range' 0 (limit + 1).toNat) (answer sides))
    rw [model] at executed
    apply Evaluates.list_comp_range (finalEnv := finalEnv) (.cons bound .nil) rfl
    simpa only [comprehensionFilters, comprehensionBody, body, masked, numbers, HeapCollection.working,
      List.nil_append] using executed
  · have empty : (limit + 1).toNat = 0 := by omega
    apply Evaluates.list_comp_range (finalEnv := masked) (.cons bound .nil) rfl
    simp only [ProjectEulerSolutions.PolygonalCycle.fourDigit, empty, List.range_zero]
    simp
    apply BlockContinues.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockContinues.nil

private def references (baseSize count : Nat) : List Mutable.Value :=
  (List.range count).map (fun index => .ref (baseSize + 1 + index))
private def objects (limit : Int) (kinds : List Nat) : Mutable.Heap :=
  kinds.map (fun kind : Nat => .list (numbers (ProjectEulerSolutions.PolygonalCycle.fourDigit limit kind)))

def tableHeap (caller : Mutable.Heap) (limit : Int) (kinds : List Nat) : Mutable.Heap :=
  HeapCollection.working caller (references caller.length kinds.length) (objects limit kinds)

private theorem tableHeap_grown (caller : Mutable.Heap) (limit : Int) (before : List Nat) (kind : Nat) :
    HeapCollection.working caller
      (references caller.length before.length ++ [.ref (tableHeap caller limit before).length])
      (objects limit before ++ [.list (numbers (ProjectEulerSolutions.PolygonalCycle.fourDigit limit kind))]) =
      tableHeap caller limit (before ++ [kind]) := by
  simp [tableHeap, references, objects, HeapCollection.working, List.range_succ, Nat.add_assoc]
  omega

private def outerBody (collector : Nat) : List Stmt := [.comprehensionAppend collector familyExpression]

private theorem outer_loop (caller : Mutable.Heap) (limit : Int) (before : List Nat)
    (first count stop : Nat) (endAt : first + count = stop) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "sides" first stop 1 (outerBody caller.length) []]
      (tableHeap caller limit before) finalEnv (tableHeap caller limit (before ++ List.range' first count)) globals := by
  induction count generalizing before first env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "sides" (number first)
      have boundLimit : bound "limit" = some (number limit) := by simpa [bound, setLocal] using getLimit
      have evaluated := family_evaluate first limit (tableHeap caller limit before) bound rfl boundLimit globals
      have emitted : BlockContinues program bound (outerBody caller.length) (tableHeap caller limit before) bound
          (tableHeap caller limit (before ++ [first])) globals := by
        have stored := HeapCollection.emit (program := program) caller (references caller.length before.length)
          (objects limit before) [.list (numbers (ProjectEulerSolutions.PolygonalCycle.fourDigit limit first))]
          (.ref (tableHeap caller limit before).length) evaluated
        simpa only [tableHeap_grown] using stored
      obtain ⟨finalEnv, continued⟩ := ih (before ++ [first]) (first + 1) (by omega) bound boundLimit
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [outerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, if_false, List.range'_succ, List.append_assoc, List.singleton_append,
        Int.natCast_add, Int.natCast_one] using emitted.append continued

/-- All six family lists are constructed in source order, retaining their shared table. -/
theorem expression_evaluate (limit : Int) (caller : Mutable.Heap) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) (globals : Mutable.Globals := []) :
    Evaluates program env expression caller (.ref caller.length) (tableHeap caller limit (List.range' 3 6)) globals := by
  let generators : List (String × Expr × List Expr) :=
    [("sides", .call (.name "range") [.constant (.int 3), .constant (.int 9)], [])]
  let masked := comprehensionEnv env generators
  have maskedLimit : masked "limit" = some (number limit) := by
    simpa [masked, generators, comprehensionEnv, setLocal] using getLimit
  obtain ⟨finalEnv, executed⟩ := outer_loop caller limit [] 3 6 9 rfl masked maskedLimit globals
  apply Evaluates.list_comp_range (finalEnv := finalEnv) (.cons Evaluates.constant (.cons Evaluates.constant .nil)) rfl
  simpa only [masked, generators, comprehensionFilters, comprehensionBody, outerBody, tableHeap,
    references, objects, List.length_nil, List.range_zero, List.map_nil, List.nil_append,
    HeapCollection.working, List.append_nil] using executed

def setupHeap (caller : Mutable.Heap) (limit : Int) : Mutable.Heap :=
  tableHeap caller limit (List.range' 3 6) ++ [.list [.ref caller.length]]
def setupEnv (env : HeapCalls.Env) (caller : Mutable.Heap) (limit : Int) : HeapCalls.Env :=
  setLocal env "__formalsw_cell_naive_families" (.ref (tableHeap caller limit (List.range' 3 6)).length)

/-- The actual first statement of `naive` builds the six families and their closure cell. -/
theorem setup_result (limit : Int) (caller : Mutable.Heap) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) (globals : Mutable.Globals := []) :
    BlockContinues program env ((executableBody ((findFunctionIn program.body "naive").getD ([], [])).2).take 1)
      caller (setupEnv env caller limit) (setupHeap caller limit) globals := by
  change BlockContinues program env
    [.assign [.name "__formalsw_cell_naive_families"] (.list [expression])]
    caller (setupEnv env caller limit) (setupHeap caller limit) globals
  exact BlockContinues.assign (Evaluates.list (.cons (expression_evaluate limit caller env getLimit globals) .nil))

end families

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
      (number (if ProjectEulerSolutions.PolygonalCycle.closed values then values.sum else 0)) heap globals := by
  have positive : 0 < values.length := List.length_pos_iff.mpr nonempty
  let first := values[0]'positive
  let last := values[values.length - 1]'(by omega)
  have head : values[0]? = some first := List.getElem?_eq_getElem positive
  have tail : values[values.length - 1]? = some last := List.getElem?_eq_getElem (by omega)
  have closed : ProjectEulerSolutions.PolygonalCycle.closed values =
      ProjectEulerSolutions.PolygonalCycle.links last first := by
    simp [ProjectEulerSolutions.PolygonalCycle.closed, List.head?_eq_getElem?, List.getLast?_eq_getElem?, head, tail]
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
  have tested : Evaluates program env closes heap (flag (ProjectEulerSolutions.PolygonalCycle.closed values)) heap globals := by
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
  cases selected : ProjectEulerSolutions.PolygonalCycle.closed values with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply BlockReturns.branch (flag := false) (by simpa only [selected] using tested) rfl
      exact BlockReturns.return_value Evaluates.constant
  | true =>
      simp only [if_true]
      apply BlockReturns.branch (flag := true) (by simpa only [selected] using tested) rfl
      exact BlockReturns.return_value summed

end extend

theorem is_cyclic_pair_source_result (left right : Int) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    ReturnsValue program "is_cyclic_pair" [number left, number right] heap
      (flag (ProjectEulerSolutions.PolygonalCycle.links left right)) heap globals :=
  is_cyclic_pair.heap_result left right heap globals

theorem families_source_result (limit : Int) (caller : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals) :
    env "limit" = some (number limit) →
    BlockContinues program env ((executableBody ((findFunctionIn program.body "naive").getD ([], [])).2).take 1)
      caller (families.setupEnv env caller limit) (families.setupHeap caller limit) globals :=
  fun getLimit => families.setup_result limit caller env getLimit globals

theorem extend_base_source_result (values : List Int) (heap : Mutable.Heap) (path remaining : Nat)
    (familiesCell : Mutable.Value) (globals : Mutable.Globals) :
    values ≠ [] → heap[path]? = some (.list (values.map number)) → heap[remaining]? = some (.list []) →
    ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remaining, familiesCell] heap
      (number (if ProjectEulerSolutions.PolygonalCycle.closed values then values.sum else 0)) heap globals :=
  fun nonempty pathFound remainingFound => extend.closed_result values nonempty heap path remaining
    pathFound remainingFound familiesCell globals

end data.«project-euler-statements».data.py.project_euler_statements.p61
