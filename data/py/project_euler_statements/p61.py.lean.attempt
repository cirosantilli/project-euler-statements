import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p61.py.ast»
import FormalSW
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ProjectEulerSolutions.Lib.PolygonalCycle
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.HeapLoop
import ProjectEulerSolutions.Lib.HeapSequenceFold
import ProjectEulerSolutions.Lib.PolygonalCycleReference.Certificate

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

structure Bindings (env : HeapCalls.Env) (path remainingAddress familiesCell : Nat) : Prop where
  getPath : env "path" = some (.ref path)
  getRemaining : env "remaining" = some (.ref remainingAddress)
  getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell)

theorem Bindings.local (bound : Bindings env path remainingAddress familiesCell) (name : String) (value : Mutable.Value)
    (fresh : name ∉ ["path", "remaining", "__formalsw_cell_naive_families"]) :
    Bindings (setLocal env name value) path remainingAddress familiesCell := by
  simp only [List.mem_cons, not_or] at fresh
  refine ⟨?_, ?_, ?_⟩ <;> simp_all [setLocal, eq_comm, bound.getPath, bound.getRemaining, bound.getCell]

theorem Bindings.function (path remainingAddress familiesCell : Nat) (globals : Mutable.Globals) :
    Bindings (functionEnv
      ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).1
      ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).2
      [.ref path, .ref remainingAddress, .ref familiesCell] globals) path remainingAddress familiesCell := by
  constructor <;> cases globals <;> rfl

def advance (values : List Int) (last : Int) (visit : Int → Int) (best value : Int) : Int :=
  if value ∈ values then best else
    if ProjectEulerSolutions.PolygonalCycle.links last value then max best (visit value) else best

/-- The actual candidate loop computes the guarded maximum and retains all child heap effects. -/
theorem candidate_loop (state : SearchState heap path remainingAddress familiesCell limit values remaining)
    (bound : Bindings env path remainingAddress familiesCell) (last : Int) (atEnd : values.getLast? = some last)
    (kind unused : Nat)
    (unusedFound : heap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))))
    (getUnused : env "unused" = some (.ref unused)) (best : Int) (getBest : env "best" = some (number best))
    (all : List Int) (source : Nat) (found : heap[source]? = some (.list (numbers all))) (visit : Int → Int)
    (child : ∀ currentHeap value, SearchState currentHeap path remainingAddress familiesCell limit values remaining →
      currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) →
      value ∈ all → value ∉ values → ProjectEulerSolutions.PolygonalCycle.links last value = true →
      ∃ extra, ReturnsValue program "__formalsw_local_naive_extend"
        [.ref (currentHeap.length + 1), .ref unused, .ref familiesCell] (childHeap currentHeap values value)
        (number (visit value)) (childHeap currentHeap values value ++ extra) globals) :
    ∃ extra finalEnv, BlockContinues program env [.sequenceStepLoop "value" (.ref source) 0 innerBody []]
      heap finalEnv (heap ++ extra) globals ∧ Bindings finalEnv path remainingAddress familiesCell ∧
      finalEnv "best" = some (number (all.foldl (advance values last visit) best)) ∧
      HeapRangeFold.Frame ["value", "best"] env finalEnv := by
  let invariant := fun currentHeap currentEnv currentBest =>
    Nonempty (SearchState currentHeap path remainingAddress familiesCell limit values remaining) ∧
      Bindings currentEnv path remainingAddress familiesCell ∧ currentEnv "unused" = some (.ref unused) ∧
      currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) ∧
      currentEnv "best" = some (number currentBest)
  have bindInvariant : ∀ currentHeap currentEnv currentBest value, invariant currentHeap currentEnv currentBest → value ∈ all →
      invariant currentHeap (setLocal currentEnv "value" (number value)) currentBest := by
    intro currentHeap currentEnv currentBest value good _
    obtain ⟨ready, currentBound, currentUnused, currentFound, currentBestFound⟩ := good
    refine ⟨ready, currentBound.local "value" (number value) (by decide), ?_, currentFound, ?_⟩
    · simpa [setLocal] using currentUnused
    · simpa [setLocal] using currentBestFound
  have cell : ∀ currentHeap currentEnv currentBest value, invariant currentHeap currentEnv currentBest → value ∈ all →
      currentEnv "value" = some (number value) →
      ∃ extra finalEnv, HeapLoop.Continues program currentEnv innerBody currentHeap finalEnv (currentHeap ++ extra) globals ∧
        invariant (currentHeap ++ extra) finalEnv (advance values last visit currentBest value) ∧
        HeapRangeFold.Frame ["value", "best"] currentEnv finalEnv := by
    intro currentHeap currentEnv currentBest value good member getValue
    obtain ⟨⟨current⟩, currentBound, currentUnused, currentFound, currentBestFound⟩ := good
    have unchanged : invariant currentHeap currentEnv currentBest :=
      ⟨⟨current⟩, currentBound, currentUnused, currentFound, currentBestFound⟩
    by_cases used : value ∈ values
    · refine ⟨[], currentEnv, ?_, ?_, HeapRangeFold.Frame.refl _ _⟩
      · simpa only [List.append_nil] using inner_used values currentHeap path current.pathFound value used currentEnv
          currentBound.getPath getValue globals
      · simpa only [advance, if_pos used, List.append_nil] using unchanged
    · cases linked : ProjectEulerSolutions.PolygonalCycle.links last value with
      | false =>
          refine ⟨[], currentEnv, ?_, ?_, HeapRangeFold.Frame.refl _ _⟩
          · simpa only [List.append_nil] using inner_unlinked values last atEnd currentHeap path current.pathFound value used linked
              currentEnv currentBound.getPath getValue globals
          · simpa only [advance, if_neg used, linked, Bool.false_eq_true, if_false, List.append_nil] using unchanged
      | true =>
          obtain ⟨extra, returned⟩ := child currentHeap value current currentFound member used linked
          let total : Mutable.Heap := [.list [number value], .list (numbers (values ++ [value]))] ++ extra
          have layout : childHeap currentHeap values value ++ extra = currentHeap ++ total := by
            simp only [childHeap, total, List.append_assoc]
          rw [layout] at returned
          let finalEnv := setLocal currentEnv "best" (number (max currentBest (visit value)))
          have finalGood : invariant (currentHeap ++ total) finalEnv (max currentBest (visit value)) := by
            refine ⟨⟨current.append total⟩, currentBound.local "best" _ (by decide), ?_, ?_, rfl⟩
            · simpa [finalEnv, setLocal] using currentUnused
            · exact HeapCollection.prefix_found _ _ _ _ currentFound
          refine ⟨total, finalEnv, ?_, ?_, HeapRangeFold.Frame.updated _ currentEnv "best" _ (by decide)⟩
          · exact inner_updated values last atEnd currentHeap path unused familiesCell current.pathFound value currentBest
              (visit value) used linked currentEnv currentBound.getPath getValue currentUnused currentBestFound currentBound.getCell returned
          · simpa only [advance, if_neg used, linked, if_true] using finalGood
  obtain ⟨extra, finalEnv, executed, good, frame⟩ := HeapLoop.fold program "value" innerBody rfl ["value", "best"] (by decide)
    number (advance values last visit) invariant source all bindInvariant cell all 0 rfl heap env best
    ⟨⟨state⟩, bound, getUnused, unusedFound, getBest⟩ found
  exact ⟨extra, finalEnv, executed, good.2.1, good.2.2.2.2, frame⟩

def advanceKind (limit : Int) (values : List Int) (last : Int) (visit : Nat → Int → Int) (best : Int) (kind : Nat) : Int :=
  (ProjectEulerSolutions.PolygonalCycle.fourDigit limit (3 + (kind : Int))).foldl (advance values last (visit kind)) best

/-- The source's type loop composes unused-type construction with the complete candidate fold. -/
theorem type_loop (state : SearchState heap path remainingAddress familiesCell limit values remaining)
    (bound : Bindings env path remainingAddress familiesCell) (last : Int) (atEnd : values.getLast? = some last)
    (best : Int) (getBest : env "best" = some (number best)) (visit : Nat → Int → Int)
    (child : ∀ currentHeap kind unused value, SearchState currentHeap path remainingAddress familiesCell limit values remaining →
      kind ∈ remaining →
      currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) →
      value ∈ ProjectEulerSolutions.PolygonalCycle.fourDigit limit (3 + (kind : Int)) → value ∉ values →
      ProjectEulerSolutions.PolygonalCycle.links last value = true →
      ∃ extra, ReturnsValue program "__formalsw_local_naive_extend"
        [.ref (currentHeap.length + 1), .ref unused, .ref familiesCell] (childHeap currentHeap values value)
        (number (visit kind value)) (childHeap currentHeap values value ++ extra) globals) :
    ∃ extra finalEnv, BlockContinues program env [.forIn (.name "kind") (.name "remaining") outerBody []]
      heap finalEnv (heap ++ extra) globals ∧ Bindings finalEnv path remainingAddress familiesCell ∧
      finalEnv "best" = some (number (remaining.foldl (advanceKind limit values last visit) best)) ∧
      HeapRangeFold.Frame ["kind", "unused", "value", "best"] env finalEnv := by
  let invariant := fun currentHeap currentEnv currentBest =>
    Nonempty (SearchState currentHeap path remainingAddress familiesCell limit values remaining) ∧
      Bindings currentEnv path remainingAddress familiesCell ∧ currentEnv "best" = some (number currentBest)
  have bindInvariant : ∀ currentHeap currentEnv currentBest kind, invariant currentHeap currentEnv currentBest → kind ∈ remaining →
      invariant currentHeap (setLocal currentEnv "kind" (number kind)) currentBest := by
    intro currentHeap currentEnv currentBest kind good _
    obtain ⟨ready, currentBound, currentBestFound⟩ := good
    exact ⟨ready, currentBound.local "kind" _ (by decide), by simpa [setLocal] using currentBestFound⟩
  have cell : ∀ currentHeap currentEnv currentBest kind, invariant currentHeap currentEnv currentBest → kind ∈ remaining →
      currentEnv "kind" = some (number kind) →
      ∃ afterEnv finalHeap, BlockContinues program currentEnv outerBody currentHeap afterEnv finalHeap globals ∧
        invariant finalHeap afterEnv (advanceKind limit values last visit currentBest kind) ∧
        (∃ extra, finalHeap = currentHeap ++ extra) ∧
        HeapRangeFold.Frame ["kind", "unused", "value", "best"] currentEnv afterEnv := by
    intro currentHeap currentEnv currentBest kind good member getKind
    obtain ⟨⟨current⟩, currentBound, currentBestFound⟩ := good
    let filtered := remaining.filter (fun other => decide (other ≠ kind))
    let middle := currentHeap ++ [.list (kinds filtered)]
    let readyEnv := setLocal currentEnv "unused" (.ref currentHeap.length)
    let ready := current.append [.list (kinds filtered)]
    have readyBound : Bindings readyEnv path remainingAddress familiesCell := currentBound.local "unused" _ (by decide)
    have readyBest : readyEnv "best" = some (number currentBest) := by simpa [readyEnv, setLocal] using currentBestFound
    have readyKind : readyEnv "kind" = some (number kind) := by simpa [readyEnv, setLocal] using getKind
    have made := unused_evaluate remaining kind currentHeap remainingAddress current.remainingFound currentEnv
      currentBound.getRemaining getKind globals
    have looked := family_evaluate ready.world kind (current.validKinds kind member) readyEnv readyBound.getCell readyKind globals
    obtain ⟨extra, finalEnv, scanned, finalBound, finalBest, frame⟩ := candidate_loop ready readyBound last atEnd kind currentHeap.length
      (by simp [filtered]) rfl currentBest readyBest
      (ProjectEulerSolutions.PolygonalCycle.fourDigit limit (3 + (kind : Int))) (ready.world.target kind)
      (ready.world.familyFound kind (current.validKinds kind member)) (visit kind)
      (fun nextHeap value ready found inFamily fresh linked => child nextHeap kind currentHeap.length value ready member found inFamily fresh linked)
    have header : BlockContinues program readyEnv [.forIn (.name "value") familyExpression innerBody []]
        middle finalEnv (middle ++ extra) globals := by
      apply BlockContinues.for_sequence (items := numbers (ProjectEulerSolutions.PolygonalCycle.fourDigit limit (3 + (kind : Int))))
        (by intro expressions impossible; cases impossible) looked
        (by simp [Mutable.sequence, ready.world.familyFound kind (current.validKinds kind member)])
      exact scanned
    have emitted := (BlockContinues.assign (name := "unused") made).append header
    let total : Mutable.Heap := .list (kinds filtered) :: extra
    have layout : middle ++ extra = currentHeap ++ total := by simp [middle, total, List.append_assoc]
    rw [layout] at emitted
    have widened : HeapRangeFold.Frame ["kind", "unused", "value", "best"] readyEnv finalEnv := by
      intro name outside
      exact frame name (fun member => outside (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
    refine ⟨finalEnv, currentHeap ++ total, emitted, ⟨⟨current.append total⟩, finalBound, finalBest⟩,
      ⟨total, rfl⟩, ?_⟩
    exact (HeapRangeFold.Frame.updated _ currentEnv "unused" (.ref currentHeap.length) (by decide)).trans widened
  obtain ⟨finalEnv, finalHeap, executed, good, ⟨extra, layout⟩, frame⟩ := HeapSequenceFold.for_list program "kind" outerBody rfl
    ["kind", "unused", "value", "best"] (by decide) (fun kind : Nat => number kind)
    (advanceKind limit values last visit) invariant remainingAddress remaining bindInvariant cell heap env best
    ⟨⟨state⟩, bound, getBest⟩ (.name "remaining") (by intro expressions impossible; cases impossible)
    (Evaluates.lookup bound.getRemaining) state.remainingFound
  rw [layout] at executed
  exact ⟨extra, finalEnv, executed, good.2.1, good.2.2, frame⟩

theorem unused_shorter (remaining : List Nat) (kind : Nat) (member : kind ∈ remaining) :
    (remaining.filter (fun other => decide (other ≠ kind))).length < remaining.length := by
  have bound := List.length_filter_le (fun other : Nat => decide (other ≠ kind)) remaining
  have different : (remaining.filter (fun other => decide (other ≠ kind))).length ≠ remaining.length := by
    intro equal
    have accepted := (List.length_filter_eq_length_iff.mp equal) kind member
    simp at accepted
  omega

private theorem empty_result (fuel : Nat) (limit : Int) (values : List Int) (nonempty : values ≠ [])
    (heap : Mutable.Heap) (path remainingAddress familiesCell : Nat)
    (pathFound : heap[path]? = some (.list (numbers values))) (remainingFound : heap[remainingAddress]? = some (.list []))
    (globals : Mutable.Globals) :
    ∃ extra, ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remainingAddress, .ref familiesCell]
      heap (number (ProjectEulerSolutions.PolygonalCycle.extend limit fuel values [])) (heap ++ extra) globals := by
  have model : ProjectEulerSolutions.PolygonalCycle.extend limit fuel values [] =
      (if ProjectEulerSolutions.PolygonalCycle.closed values then values.sum else 0) := by cases fuel <;> rfl
  refine ⟨[], ?_⟩
  rw [model]
  simpa only [List.append_nil] using closed_result values nonempty heap path remainingAddress pathFound remainingFound (.ref familiesCell) globals

/-- The full recursive reference search terminates and returns its exact maximum-search model. -/
theorem search_result (fuel : Nat) (heap : Mutable.Heap) (path remainingAddress familiesCell : Nat) (limit : Int)
    (values : List Int) (remaining : List Nat)
    (state : SearchState heap path remainingAddress familiesCell limit values remaining)
    (nonempty : values ≠ []) (depth : remaining.length ≤ fuel) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remainingAddress, .ref familiesCell]
      heap (number (ProjectEulerSolutions.PolygonalCycle.extend limit fuel values remaining)) (heap ++ extra) globals := by
  induction fuel generalizing heap path remainingAddress familiesCell limit values remaining with
  | zero =>
      have empty : remaining = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst remaining
      exact empty_result 0 limit values nonempty heap path remainingAddress familiesCell state.pathFound state.remainingFound globals
  | succ fuel ih =>
      by_cases empty : remaining = []
      · subst remaining
        exact empty_result (fuel + 1) limit values nonempty heap path remainingAddress familiesCell state.pathFound state.remainingFound globals
      · obtain ⟨last, atEnd⟩ : ∃ last, values.getLast? = some last := by
          cases found : values.getLast? with
          | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp found))
          | some last => exact ⟨last, rfl⟩
        have noTypes : remaining.isEmpty = false := by
          cases remaining with
          | nil => exact False.elim (empty rfl)
          | cons _ _ => rfl
        let params := ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).1
        let sourceBody := ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).2
        let env := functionEnv params sourceBody [.ref path, .ref remainingAddress, .ref familiesCell] globals
        have bound : Bindings env path remainingAddress familiesCell := Bindings.function path remainingAddress familiesCell globals
        let bestEnv := setLocal env "best" (number 0)
        have bestBound : Bindings bestEnv path remainingAddress familiesCell := bound.local "best" _ (by decide)
        let visit := fun kind value => ProjectEulerSolutions.PolygonalCycle.extend limit fuel (values ++ [value])
          (remaining.filter (fun other => decide (other ≠ kind)))
        have child : ∀ currentHeap kind unused value,
            SearchState currentHeap path remainingAddress familiesCell limit values remaining → kind ∈ remaining →
            currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) →
            value ∈ ProjectEulerSolutions.PolygonalCycle.fourDigit limit (3 + (kind : Int)) → value ∉ values →
            ProjectEulerSolutions.PolygonalCycle.links last value = true →
            ∃ extra, ReturnsValue program "__formalsw_local_naive_extend"
              [.ref (currentHeap.length + 1), .ref unused, .ref familiesCell] (childHeap currentHeap values value)
              (number (visit kind value)) (childHeap currentHeap values value ++ extra) globals := by
          intro currentHeap kind unused value ready member unusedFound _ _ _
          have smaller := unused_shorter remaining kind member
          exact ih (childHeap currentHeap values value) (currentHeap.length + 1) unused familiesCell limit
            (values ++ [value]) (remaining.filter (fun other => decide (other ≠ kind)))
            (ready.child kind value unused unusedFound) (by simp) (by omega)
        obtain ⟨extra, finalEnv, executed, finalBound, finalBest, frame⟩ :=
          type_loop state bestBound last atEnd 0 rfl visit child
        have model : ProjectEulerSolutions.PolygonalCycle.extend limit (fuel + 1) values remaining =
            remaining.foldl (advanceKind limit values last visit) 0 := by
          rw [ProjectEulerSolutions.PolygonalCycle.extend, noTypes]
          simp only [Bool.false_eq_true, if_false, atEnd, Option.getD_some]
          rfl
        refine ⟨extra, ?_⟩
        rw [model]
        apply BlockReturns.function rfl rfl
        change BlockReturns program env code heap _ (heap ++ extra) globals
        have tested : Evaluates program env exhausted heap (flag false) heap globals := by
          apply Evaluates.unary (middle := heap) (finalHeap := heap) (Evaluates.lookup bound.getRemaining)
          simp [HeapCalls.unary, Mutable.truth, state.remainingFound, kinds, noTypes, flag]
        apply BlockReturns.branch (flag := false) tested rfl
        apply BlockReturns.assign Evaluates.constant
        exact BlockContinues.returns executed (BlockReturns.return_value (Evaluates.lookup finalBest))

end extend

namespace naive
private abbrev numbers := extend.numbers
private abbrev kinds := extend.kinds
def types : List Nat := [1, 2, 3, 4, 5]
def startValue (limit start : Int) : Int := ProjectEulerSolutions.PolygonalCycle.extend limit 5 [start] types
def startArguments : List Expr :=
  [.list [.name "start"], .list [.constant (.int 1), .constant (.int 2), .constant (.int 3),
    .constant (.int 4), .constant (.int 5)], .name "__formalsw_cell_naive_families"]
def startCall : Expr := .call (.name "__formalsw_local_naive_extend") startArguments
def startIterable : Expr := .subscript
  (.subscript (.name "__formalsw_cell_naive_families") (.constant (.int 0))) (.constant (.int 0))
def startBody : List Stmt := [.assign [.name "best"] (.builtinCall .max [.name "best", startCall])]
def code : List Stmt :=
  [.assign [.name "__formalsw_cell_naive_families"] (.list [families.expression]),
   .assign [.name "best"] (.constant (.int 0)), .forIn (.name "start") startIterable startBody [], .return (.name "best")]

theorem code_source : executableBody ((findFunctionIn program.body "naive").getD ([], [])).2 = code := rfl

def startHeap (heap : Mutable.Heap) (start : Int) : Mutable.Heap := heap ++ [.list [number start], .list (kinds types)]

theorem arguments_evaluate (heap : Mutable.Heap) (start : Int) (familiesCell : Nat) (env : HeapCalls.Env)
    (getStart : env "start" = some (number start))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell)) (globals : Mutable.Globals := []) :
    Evaluates.Arguments program env startArguments heap [.ref heap.length, .ref (heap.length + 1), .ref familiesCell]
      (startHeap heap start) globals := by
  have pathRun : Evaluates program env (.list [.name "start"]) heap (.ref heap.length)
      (heap ++ [.list [number start]]) globals := Evaluates.list (.cons (Evaluates.lookup getStart) .nil)
  have remainingRun : Evaluates program env
      (.list [.constant (.int 1), .constant (.int 2), .constant (.int 3), .constant (.int 4), .constant (.int 5)])
      (heap ++ [.list [number start]]) (.ref (heap.length + 1)) (startHeap heap start) globals := by
    have evaluated : Evaluates program env
        (.list [.constant (.int 1), .constant (.int 2), .constant (.int 3), .constant (.int 4), .constant (.int 5)])
        (heap ++ [.list [number start]]) (.ref (heap ++ [Mutable.Object.list [number start]]).length)
        ((heap ++ [.list [number start]]) ++ [.list (kinds types)]) globals :=
      Evaluates.list (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant
        (.cons Evaluates.constant (.cons Evaluates.constant .nil)))))
    simpa [startHeap, List.append_assoc] using evaluated
  exact .cons pathRun (.cons remainingRun (.cons (Evaluates.lookup getCell) .nil))

variable {heap : Mutable.Heap} {familiesCell : Nat} {limit : Int}

def startState (world : extend.World heap familiesCell limit) (start : Int) :
    extend.SearchState (startHeap heap start) heap.length (heap.length + 1) familiesCell limit [start] types where
  world := world.append [.list [number start], .list (kinds types)]
  pathFound := by simp [startHeap, extend.numbers]
  remainingFound := by simp [startHeap]
  validKinds := by intro kind member; simp [types] at member; omega

theorem start_evaluate (world : extend.World heap familiesCell limit) (start : Int) (env : HeapCalls.Env)
    (getStart : env "start" = some (number start))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell)) (globals : Mutable.Globals := []) :
    ∃ extra, Evaluates program env startCall heap (number (startValue limit start)) (heap ++ extra) globals := by
  obtain ⟨extra, returned⟩ := extend.search_result 5 (startHeap heap start) heap.length (heap.length + 1)
    familiesCell limit [start] types (startState world start) (by simp) (by decide) globals
  let total := [.list [number start], .list (kinds types)] ++ extra
  have layout : startHeap heap start ++ extra = heap ++ total := by simp only [startHeap, total, List.append_assoc]
  refine ⟨total, ?_⟩
  rw [← layout]
  exact Evaluates.call (arguments_evaluate heap start familiesCell env getStart getCell globals) returned

theorem iterable_evaluate (world : extend.World heap familiesCell limit) (env : HeapCalls.Env)
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell)) (globals : Mutable.Globals := []) :
    Evaluates program env startIterable heap (.ref (world.target 0)) heap globals := by
  have table : Evaluates program env
      (.subscript (.name "__formalsw_cell_naive_families") (.constant (.int 0))) heap (.ref world.table) heap globals := by
    apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getCell) Evaluates.constant
    exact Mutable.getItem_list _ _ 0 [.ref world.table] world.cellFound (by simp)
  apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
    (by intros; intro impossible; cases impossible) table Evaluates.constant
  have found := Mutable.getItem_list heap world.table 0 ((List.range 6).map (fun kind => .ref (world.target kind)))
    world.tableFound (by simp)
  simpa using found

theorem start_loop (world : extend.World heap familiesCell limit) (env : HeapCalls.Env)
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (best : Int) (getBest : env "best" = some (number best)) (globals : Mutable.Globals := []) :
    ∃ extra finalEnv, BlockContinues program env [.forIn (.name "start") startIterable startBody []] heap finalEnv (heap ++ extra) globals ∧
      finalEnv "best" = some (number ((ProjectEulerSolutions.PolygonalCycle.fourDigit limit 3).foldl
        (fun best start => max best (startValue limit start)) best)) := by
  let invariant := fun (currentHeap : Mutable.Heap) (currentEnv : HeapCalls.Env) (currentBest : Int) =>
    Nonempty (extend.World currentHeap familiesCell limit) ∧
    currentEnv "__formalsw_cell_naive_families" = some (.ref familiesCell) ∧ currentEnv "best" = some (number currentBest)
  have bindInvariant : ∀ currentHeap currentEnv currentBest start, invariant currentHeap currentEnv currentBest →
      start ∈ ProjectEulerSolutions.PolygonalCycle.fourDigit limit 3 →
      invariant currentHeap (setLocal currentEnv "start" (number start)) currentBest := by
    intro currentHeap currentEnv currentBest start good _
    exact ⟨good.1, by simpa [setLocal] using good.2.1, by simpa [setLocal] using good.2.2⟩
  have cell : ∀ currentHeap currentEnv currentBest start, invariant currentHeap currentEnv currentBest →
      start ∈ ProjectEulerSolutions.PolygonalCycle.fourDigit limit 3 → currentEnv "start" = some (number start) →
      ∃ finalEnv finalHeap, BlockContinues program currentEnv startBody currentHeap finalEnv finalHeap globals ∧
        invariant finalHeap finalEnv (max currentBest (startValue limit start)) ∧
        (∃ extra, finalHeap = currentHeap ++ extra) ∧ HeapRangeFold.Frame ["start", "best"] currentEnv finalEnv := by
    intro currentHeap currentEnv currentBest start good _ getStart
    obtain ⟨⟨current⟩, currentCell, currentBestFound⟩ := good
    obtain ⟨extra, evaluated⟩ := start_evaluate current start currentEnv getStart currentCell globals
    have maximum : Evaluates program currentEnv (.builtinCall .max [.name "best", startCall]) currentHeap
        (number (max currentBest (startValue limit start))) (currentHeap ++ extra) globals := by
      apply Evaluates.builtin (.cons (Evaluates.lookup currentBestFound) (.cons evaluated .nil))
      by_cases better : currentBest < startValue limit start
      · simp [primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp, scalarResult,
          better, Int.max_eq_right (by omega : currentBest ≤ startValue limit start)]
      · simp [primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp, scalarResult,
          better, Int.max_eq_left (by omega : startValue limit start ≤ currentBest)]
    refine ⟨setLocal currentEnv "best" (number (max currentBest (startValue limit start))), currentHeap ++ extra,
      BlockContinues.assign maximum, ⟨⟨current.append extra⟩, ?_, rfl⟩, ⟨extra, rfl⟩,
      HeapRangeFold.Frame.updated _ currentEnv "best" _ (by decide)⟩
    simpa [setLocal] using currentCell
  obtain ⟨finalEnv, finalHeap, executed, good, ⟨extra, layout⟩, frame⟩ := HeapSequenceFold.for_list program "start" startBody rfl
    ["start", "best"] (by decide) number (fun best start => max best (startValue limit start)) invariant
    (world.target 0) (ProjectEulerSolutions.PolygonalCycle.fourDigit limit 3) bindInvariant cell heap env best
    ⟨⟨world⟩, getCell, getBest⟩ startIterable (by intro expressions impossible; cases impossible)
    (iterable_evaluate world env getCell globals) (world.familyFound 0 (by decide))
  rw [layout] at executed
  exact ⟨extra, finalEnv, executed, good.2.2⟩

/-- The complete reference source returns its exhaustive model for every signed limit. -/
theorem heap_result (limit : Int) (caller : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number limit] caller
      (number (ProjectEulerSolutions.PolygonalCycle.reference limit)) (caller ++ extra) globals := by
  let params := ((findFunctionIn program.body "naive").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
  let env := functionEnv params sourceBody [number limit] globals
  have getLimit : env "limit" = some (number limit) := by cases globals <;> rfl
  have setup := families.setup_result limit caller env getLimit globals
  let readyEnv := setLocal (families.setupEnv env caller limit) "best" (number 0)
  obtain ⟨extra, finalEnv, searched, finalBest⟩ := start_loop (extend.World.of_setup caller limit) readyEnv
    (by simp [readyEnv, families.setupEnv, setLocal]) 0 rfl globals
  change finalEnv "best" = some (number (ProjectEulerSolutions.PolygonalCycle.reference limit)) at finalBest
  let setupExtra := (.list (families.references caller.length (List.range' 3 6).length) ::
    families.objects limit (List.range' 3 6)) ++ [.list [.ref caller.length]]
  have layout : families.setupHeap caller limit ++ extra = caller ++ (setupExtra ++ extra) := by
    simp only [families.setupHeap, families.tableHeap, HeapCollection.working, setupExtra, List.append_assoc]
  refine ⟨setupExtra ++ extra, ?_⟩
  rw [← layout]
  apply BlockReturns.function rfl rfl
  have tail : BlockReturns program (families.setupEnv env caller limit) ((executableBody sourceBody).drop 1)
      (families.setupHeap caller limit) (number (ProjectEulerSolutions.PolygonalCycle.reference limit))
      (families.setupHeap caller limit ++ extra) globals := by
    change BlockReturns program (families.setupEnv env caller limit)
      [.assign [.name "best"] (.constant (.int 0)), .forIn (.name "start") startIterable startBody [], .return (.name "best")] _ _ _ globals
    apply BlockReturns.assign Evaluates.constant
    exact BlockContinues.returns searched (BlockReturns.return_value (Evaluates.lookup finalBest))
  have complete := BlockContinues.returns setup tail
  simpa only [List.take_append_drop] using complete

theorem «Returns» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  obtain ⟨extra, returned⟩ := heap_result limit []
  exact returned.scalar_returns (values := [.int limit])

theorem «Supported» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported := («Returns» limit).supported
end naive

namespace naive_default
theorem heap_result (caller : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive_default" [] caller (number 28684) (caller ++ extra) globals := by
  obtain ⟨extra, returned⟩ := naive.heap_result 140 caller globals
  rw [ProjectEulerSolutions.PolygonalCycle.Reference.reference_checked] at returned
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons Evaluates.constant .nil) returned

theorem «Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨extra, returned⟩ := heap_result []
  exact returned.scalar_returns

theorem «Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported := «Returns».supported
end naive_default

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

theorem extend_source_result (fuel : Nat) (heap : Mutable.Heap) (path remainingAddress familiesCell : Nat) (limit : Int)
    (values : List Int) (remaining : List Nat)
    (state : extend.SearchState heap path remainingAddress familiesCell limit values remaining) (globals : Mutable.Globals) :
    values ≠ [] → remaining.length ≤ fuel →
    ∃ extra, ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remainingAddress, .ref familiesCell]
      heap (number (ProjectEulerSolutions.PolygonalCycle.extend limit fuel values remaining)) (heap ++ extra) globals :=
  fun nonempty depth => extend.search_result fuel heap path remainingAddress familiesCell limit values remaining state nonempty depth globals

theorem naive_source_result (limit : Int) (caller : Mutable.Heap) (globals : Mutable.Globals) :
    ∃ extra, ReturnsValue program "naive" [number limit] caller (number (ProjectEulerSolutions.PolygonalCycle.reference limit))
      (caller ++ extra) globals := naive.heap_result limit caller globals

end data.«project-euler-statements».data.py.project_euler_statements.p61
