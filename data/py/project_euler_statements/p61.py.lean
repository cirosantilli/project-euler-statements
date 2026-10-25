import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p61.py.ast»
import FormalSW
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ProjectEulerSolutions.Lib.PolygonalCycle
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.HeapLoop

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

def familyExpression : Expr := .subscript
  (.subscript (.name "__formalsw_cell_naive_families") (.constant (.int 0))) (.name "kind")
def unusedFilter : Expr := .compare (.name "other") [(.notEq, .name "kind")]
def unusedExpression : Expr := .listComp (.name "other") [("other", .name "remaining", [unusedFilter])]
def extendedPath : Expr := .binOp (.name "path") .add (.list [.name "value"])
def childArguments : List Expr := [extendedPath, .name "unused", .name "__formalsw_cell_naive_families"]
def childCall : Expr := .call (.name "__formalsw_local_naive_extend") childArguments
def innerBody : List Stmt :=
  [.ifThen (.membership (.name "value") (.name "path") false) [.continueLoop] [],
   .ifThen (.unaryOp .not (.call (.name "is_cyclic_pair")
     [.subscript (.name "path") (.unaryOp .uSub (.constant (.int 1))), .name "value"])) [.continueLoop] [],
   .assign [.name "best"] (.builtinCall .max [.name "best", childCall])]
def outerBody : List Stmt :=
  [.assign [.name "unused"] unusedExpression, .forIn (.name "value") familyExpression innerBody []]
def code : List Stmt :=
  [.ifThen exhausted baseBody [], .assign [.name "best"] (.constant (.int 0)),
   .forIn (.name "kind") (.name "remaining") outerBody [], .return (.name "best")]

theorem code_source :
    executableBody ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).2 = code := rfl

/-- Read-only captured family lists, indexed by the reference's six type numbers. -/
structure World (heap : Mutable.Heap) (familiesCell : Nat) (limit : Int) where
  table : Nat
  target : Nat → Nat
  cellFound : heap[familiesCell]? = some (.list [.ref table])
  tableFound : heap[table]? = some (.list ((List.range 6).map (fun kind => .ref (target kind))))
  familyFound : ∀ kind, kind < 6 → heap[target kind]? =
    some (.list (numbers (ProjectEulerSolutions.PolygonalCycle.fourDigit limit (3 + (kind : Int)))))

variable {heap : Mutable.Heap} {familiesCell : Nat} {limit : Int}

def World.append (world : World heap familiesCell limit) (extra : Mutable.Heap) :
    World (heap ++ extra) familiesCell limit where
  table := world.table
  target := world.target
  cellFound := HeapCollection.prefix_found _ _ _ _ world.cellFound
  tableFound := HeapCollection.prefix_found _ _ _ _ world.tableFound
  familyFound := fun kind valid => HeapCollection.prefix_found _ _ _ _ (world.familyFound kind valid)

def World.of_setup (caller : Mutable.Heap) (limit : Int) :
    World (families.setupHeap caller limit) (families.tableHeap caller limit (List.range' 3 6)).length limit where
  table := caller.length
  target := fun kind => caller.length + 1 + kind
  cellFound := by simp [families.setupHeap]
  tableFound := by
    simp [families.setupHeap, families.tableHeap, HeapCollection.working, families.references]
  familyFound := by
    intro kind valid
    have cases : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [families.setupHeap, families.tableHeap, HeapCollection.working, families.objects, List.range',
        numbers, families.numbers, List.append_assoc, Nat.add_assoc]

theorem family_evaluate (world : World heap familiesCell limit) (kind : Nat) (valid : kind < 6)
    (env : HeapCalls.Env) (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (getKind : env "kind" = some (number kind)) (globals : Mutable.Globals := []) :
    Evaluates program env familyExpression heap (.ref (world.target kind)) heap globals := by
  have table : Evaluates program env
      (.subscript (.name "__formalsw_cell_naive_families") (.constant (.int 0))) heap (.ref world.table) heap globals := by
    apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getCell) Evaluates.constant
    exact Mutable.getItem_list _ _ 0 [.ref world.table] world.cellFound (by simp)
  apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
    (by intros; intro impossible; cases impossible) table (Evaluates.lookup getKind)
  have found := Mutable.getItem_list heap world.table kind ((List.range 6).map (fun kind => .ref (world.target kind)))
    world.tableFound (by simpa using valid)
  simpa using found

private def kinds (values : List Nat) : List Mutable.Value := values.map (fun value : Nat => number value)
private def unusedBody (collector : Nat) : List Stmt :=
  [.ifThen unusedFilter [.comprehensionAppend collector (.name "other")] []]

private theorem unused_loop (all remaining : List Nat) (position : Nat) (suffix : all.drop position = remaining)
    (kind : Nat) (base : Mutable.Heap) (address : Nat) (found : base[address]? = some (.list (kinds all)))
    (before : List Nat) (env : HeapCalls.Env) (getKind : env "kind" = some (number kind)) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues program env [.sequenceStepLoop "other" (.ref address) position (unusedBody base.length) []]
      (HeapCollection.working base (kinds before) []) finalEnv
      (HeapCollection.working base (kinds (before ++ remaining.filter (fun other => decide (other ≠ kind)))) []) globals := by
  have sequence (collected : List Nat) :
      Mutable.sequence (sequenceValue (.ref address)) (HeapCollection.working base (kinds collected) []) =
        some (.ok (kinds all), HeapCollection.working base (kinds collected) []) := by
    have kept := HeapCollection.prefix_found base [.list (kinds collected)] address _ found
    simpa only [HeapCollection.working, List.append_nil] using
      (show Mutable.sequence (.ref address) (base ++ [.list (kinds collected)]) =
        some (.ok (kinds all), base ++ [.list (kinds collected)]) by simp [Mutable.sequence, kept])
  induction remaining generalizing position before env with
  | nil =>
      refine ⟨env, ?_⟩
      simp only [List.filter_nil, List.append_nil]
      apply BlockContinues.sequence_done (sequence before)
      · have missing : all[position]? = none := by rw [← List.head?_drop, suffix]; rfl
        simp [kinds, List.getElem?_map, missing]
      · exact BlockContinues.nil
  | cons other rest ih =>
      have selected : all[position]? = some other := by rw [← List.head?_drop, suffix]; rfl
      let bound := setLocal env "other" (number other)
      have boundKind : bound "kind" = some (number kind) := by simpa [bound, setLocal] using getKind
      have tested : Evaluates program bound unusedFilter (HeapCollection.working base (kinds before) [])
          (flag (decide (other ≠ kind))) (HeapCollection.working base (kinds before) []) globals := by
        apply Evaluates.compare (middle := HeapCollection.working base (kinds before) [])
          (afterRight := HeapCollection.working base (kinds before) [])
          (finalHeap := HeapCollection.working base (kinds before) [])
          (Evaluates.lookup (by rfl)) (Evaluates.lookup boundKind)
        simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
      have nextSuffix : all.drop (position + 1) = rest := by
        simp only [List.drop_add_one_eq_tail_drop, suffix, List.tail_cons]
      by_cases different : other ≠ kind
      · rw [show decide (other ≠ kind) = true from decide_eq_true different] at tested
        have emitted : BlockContinues program bound (unusedBody base.length)
            (HeapCollection.working base (kinds before) []) bound
            (HeapCollection.working base (kinds (before ++ [other])) []) globals := by
          apply BlockContinues.branch (flag := true) tested rfl
          have stored := HeapCollection.emit (program := program) base (kinds before) [] [] (number other)
            (by simpa only [List.append_nil] using
              (Evaluates.lookup (module := program) (globals := globals)
                (heap := HeapCollection.working base (kinds before) []) (show bound "other" = some (number other) from rfl)))
          simpa only [kinds, List.map_append, List.map_cons, List.map_nil, List.append_nil] using stored
        obtain ⟨finalEnv, continued⟩ := ih (position + 1) nextSuffix (before ++ [other]) bound boundKind
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.sequence_step (value := number other) (sequence before) (by simp [kinds, List.getElem?_map, selected])
        simpa [unusedBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          List.filter_cons, different, List.append_assoc] using emitted.append continued
      · rw [show decide (other ≠ kind) = false from decide_eq_false different] at tested
        have skipped : BlockContinues program bound (unusedBody base.length)
            (HeapCollection.working base (kinds before) []) bound (HeapCollection.working base (kinds before) []) globals :=
          BlockContinues.branch (flag := false) tested rfl .nil
        obtain ⟨finalEnv, continued⟩ := ih (position + 1) nextSuffix before bound boundKind
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.sequence_step (value := number other) (sequence before) (by simp [kinds, List.getElem?_map, selected])
        simpa [unusedBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          List.filter_cons, different] using skipped.append continued

/-- Filtering the remaining types creates one fresh list and preserves every old object. -/
theorem unused_evaluate (all : List Nat) (kind : Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (kinds all))) (env : HeapCalls.Env)
    (getRemaining : env "remaining" = some (.ref address)) (getKind : env "kind" = some (number kind))
    (globals : Mutable.Globals := []) :
    Evaluates program env unusedExpression heap (.ref heap.length)
      (heap ++ [.list (kinds (all.filter (fun other => decide (other ≠ kind))))]) globals := by
  let masked := comprehensionEnv env [("other", .name "remaining", [unusedFilter])]
  have maskedKind : masked "kind" = some (number kind) := by
    simpa [masked, comprehensionEnv, setLocal] using getKind
  obtain ⟨finalEnv, executed⟩ := unused_loop all all 0 rfl kind heap address found [] masked maskedKind globals
  apply Evaluates.list_comp_sequence (items := kinds all) (finalEnv := finalEnv)
    (by intro expressions impossible; cases impossible) (Evaluates.lookup getRemaining)
    (by simp [Mutable.sequence, found])
  simpa only [masked, comprehensionFilters, comprehensionBody, unusedBody, HeapCollection.working,
    kinds, List.map_nil, List.nil_append, List.append_nil] using executed

def childHeap (heap : Mutable.Heap) (values : List Int) (value : Int) : Mutable.Heap :=
  heap ++ [.list [number value], .list (numbers (values ++ [value]))]

theorem path_argument_evaluate (values : List Int) (heap : Mutable.Heap) (path : Nat)
    (found : heap[path]? = some (.list (numbers values))) (value : Int) (env : HeapCalls.Env)
    (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (globals : Mutable.Globals := []) :
    Evaluates program env extendedPath heap (.ref (heap.length + 1)) (childHeap heap values value) globals := by
  have singleton : Evaluates program env (.list [.name "value"]) heap (.ref heap.length)
      (heap ++ [.list [number value]]) globals := Evaluates.list (.cons (Evaluates.lookup getValue) .nil)
  have kept := HeapCollection.prefix_found heap [.list [number value]] path _ found
  apply Evaluates.binary (middle := heap) (afterRight := heap ++ [.list [number value]])
    (Evaluates.lookup getPath) singleton
  simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, Mutable.array, kept,
    Mutable.allocate, Except.map, childHeap, numbers, List.append_assoc]

theorem child_arguments_evaluate (values : List Int) (heap : Mutable.Heap) (path unused familiesCell : Nat)
    (found : heap[path]? = some (.list (numbers values))) (value : Int) (env : HeapCalls.Env)
    (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (getUnused : env "unused" = some (.ref unused))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell)) (globals : Mutable.Globals := []) :
    Evaluates.Arguments program env childArguments heap [.ref (heap.length + 1), .ref unused, .ref familiesCell]
      (childHeap heap values value) globals :=
  .cons (path_argument_evaluate values heap path found value env getPath getValue globals)
    (.cons (Evaluates.lookup getUnused) (.cons (Evaluates.lookup getCell) .nil))

/-- Source parameters and captured tables describe the same logical reference search. -/
structure SearchState (heap : Mutable.Heap) (path remainingAddress familiesCell : Nat) (limit : Int)
    (values : List Int) (remaining : List Nat) where
  world : World heap familiesCell limit
  pathFound : heap[path]? = some (.list (numbers values))
  remainingFound : heap[remainingAddress]? = some (.list (kinds remaining))
  validKinds : ∀ kind ∈ remaining, kind < 6

def SearchState.append (state : SearchState heap path remainingAddress familiesCell limit values remaining)
    (extra : Mutable.Heap) :
    SearchState (heap ++ extra) path remainingAddress familiesCell limit values remaining where
  world := state.world.append extra
  pathFound := HeapCollection.prefix_found _ _ _ _ state.pathFound
  remainingFound := HeapCollection.prefix_found _ _ _ _ state.remainingFound
  validKinds := state.validKinds

def SearchState.child (state : SearchState heap path remainingAddress familiesCell limit values remaining)
    (kind : Nat) (value : Int) (unused : Nat)
    (unusedFound : heap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind)))))) :
    SearchState (childHeap heap values value) (heap.length + 1) unused familiesCell limit (values ++ [value])
      (remaining.filter (fun other => decide (other ≠ kind))) where
  world := state.world.append [.list [number value], .list (numbers (values ++ [value]))]
  pathFound := by simp [childHeap]
  remainingFound := HeapCollection.prefix_found _ _ _ _ unusedFound
  validKinds := by
    intro other member
    exact state.validKinds other (List.mem_filter.mp member).1

theorem membership_evaluate (values : List Int) (heap : Mutable.Heap) (path : Nat)
    (found : heap[path]? = some (.list (numbers values))) (value : Int) (env : HeapCalls.Env)
    (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (globals : Mutable.Globals := []) :
    Evaluates program env (.membership (.name "value") (.name "path") false) heap
      (flag (decide (value ∈ values))) heap globals := by
  apply Evaluates.membership (.cons (Evaluates.lookup getValue) (.cons (Evaluates.lookup getPath) .nil))
  exact HeapCalls.membership_list_ints heap path value values found false

def lastExpression : Expr := .subscript (.name "path") (.unaryOp .uSub (.constant (.int 1)))

theorem last_evaluate (values : List Int) (last : Int) (atEnd : values.getLast? = some last)
    (heap : Mutable.Heap) (path : Nat) (found : heap[path]? = some (.list (numbers values)))
    (env : HeapCalls.Env) (getPath : env "path" = some (.ref path)) (globals : Mutable.Globals := []) :
    Evaluates program env lastExpression heap (number last) heap globals := by
  have nonempty : values ≠ [] := by intro empty; simp [empty] at atEnd
  have positive : 0 < values.length := List.length_pos_iff.mpr nonempty
  have tail : values[values.length - 1]? = some last := by rw [← List.getLast?_eq_getElem?]; exact atEnd
  apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getPath)
    (Evaluates.unary (middle := heap) (finalHeap := heap) (value := number 1) Evaluates.constant rfl)
  have offset : ((-1 : Int) + values.length).toNat = values.length - 1 := by omega
  have indexed : Mutable.index (numbers values) (number (-1)) heap = some (.ok (values.length - 1), heap) := by
    simp [Mutable.index, numbers, nonempty, offset]
  have mapped : (numbers values)[values.length - 1]? = some (number last) := by simp [numbers, tail]
  simp [Mutable.getItem, found, indexed, Except.map, mapped]

theorem link_evaluate (values : List Int) (last : Int) (atEnd : values.getLast? = some last)
    (heap : Mutable.Heap) (path : Nat) (found : heap[path]? = some (.list (numbers values)))
    (value : Int) (env : HeapCalls.Env) (getPath : env "path" = some (.ref path))
    (getValue : env "value" = some (number value)) (globals : Mutable.Globals := []) :
    Evaluates program env (.unaryOp .not (.call (.name "is_cyclic_pair") [lastExpression, .name "value"])) heap
      (flag (!ProjectEulerSolutions.PolygonalCycle.links last value)) heap globals := by
  apply Evaluates.unary (middle := heap) (finalHeap := heap)
    (Evaluates.call (.cons (last_evaluate values last atEnd heap path found env getPath globals)
      (.cons (Evaluates.lookup getValue) .nil)) (is_cyclic_pair.heap_result last value heap globals))
  simp [HeapCalls.unary, Mutable.truth, scalarTruth, flag]

theorem maximum_evaluate (values : List Int) (heap : Mutable.Heap) (path unused familiesCell : Nat)
    (found : heap[path]? = some (.list (numbers values))) (value best child : Int) (env : HeapCalls.Env)
    (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (getUnused : env "unused" = some (.ref unused)) (getBest : env "best" = some (number best))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (returned : ReturnsValue program "__formalsw_local_naive_extend"
      [.ref (heap.length + 1), .ref unused, .ref familiesCell] (childHeap heap values value)
      (number child) finalHeap globals) :
    Evaluates program env (.builtinCall .max [.name "best", childCall]) heap (number (max best child)) finalHeap globals := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getBest)
    (.cons (Evaluates.call
      (child_arguments_evaluate values heap path unused familiesCell found value env getPath getValue getUnused getCell globals)
      returned) .nil))
  by_cases better : best < child
  · simp [primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp, scalarResult,
      better, Int.max_eq_right (by omega : best ≤ child)]
  · simp [primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp, scalarResult,
      better, Int.max_eq_left (by omega : child ≤ best)]

theorem inner_used (values : List Int) (heap : Mutable.Heap) (path : Nat)
    (found : heap[path]? = some (.list (numbers values))) (value : Int) (used : value ∈ values)
    (env : HeapCalls.Env) (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (globals : Mutable.Globals := []) : HeapLoop.Continues program env innerBody heap env heap globals := by
  have seen := membership_evaluate values heap path found value env getPath getValue globals
  rw [show decide (value ∈ values) = true from decide_eq_true used] at seen
  apply HeapLoop.branch (flag := true) seen rfl
  apply HeapLoop.skip
  intros
  rfl

theorem inner_unlinked (values : List Int) (last : Int) (atEnd : values.getLast? = some last)
    (heap : Mutable.Heap) (path : Nat) (found : heap[path]? = some (.list (numbers values)))
    (value : Int) (fresh : value ∉ values) (unlinked : ProjectEulerSolutions.PolygonalCycle.links last value = false)
    (env : HeapCalls.Env) (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (globals : Mutable.Globals := []) : HeapLoop.Continues program env innerBody heap env heap globals := by
  have seen := membership_evaluate values heap path found value env getPath getValue globals
  rw [show decide (value ∈ values) = false from decide_eq_false fresh] at seen
  apply HeapLoop.branch (flag := false) seen rfl
  have tested := link_evaluate values last atEnd heap path found value env getPath getValue globals
  rw [unlinked] at tested
  apply HeapLoop.branch (flag := true) tested rfl
  apply HeapLoop.skip
  intros
  rfl

theorem inner_updated (values : List Int) (last : Int) (atEnd : values.getLast? = some last)
    (heap : Mutable.Heap) (path unused familiesCell : Nat) (found : heap[path]? = some (.list (numbers values)))
    (value best child : Int) (fresh : value ∉ values) (linked : ProjectEulerSolutions.PolygonalCycle.links last value = true)
    (env : HeapCalls.Env) (getPath : env "path" = some (.ref path)) (getValue : env "value" = some (number value))
    (getUnused : env "unused" = some (.ref unused)) (getBest : env "best" = some (number best))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (returned : ReturnsValue program "__formalsw_local_naive_extend"
      [.ref (heap.length + 1), .ref unused, .ref familiesCell] (childHeap heap values value)
      (number child) finalHeap globals) :
    HeapLoop.Continues program env innerBody heap (setLocal env "best" (number (max best child))) finalHeap globals := by
  have seen := membership_evaluate values heap path found value env getPath getValue globals
  rw [show decide (value ∈ values) = false from decide_eq_false fresh] at seen
  apply HeapLoop.branch (flag := false) seen rfl
  have tested := link_evaluate values last atEnd heap path found value env getPath getValue globals
  rw [linked] at tested
  apply HeapLoop.branch (flag := false) tested rfl
  have assigned := BlockContinues.assign (name := "best")
    (maximum_evaluate values heap path unused familiesCell found value best child env getPath getValue getUnused getBest getCell returned)
  have resumed := HeapLoop.prepend assigned (HeapLoop.nil program _ _ globals)
  simpa only [List.append_nil] using resumed

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
