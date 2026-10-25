import data.«project-euler-statements».data.py.project_euler_statements.«p38.predicate.source»
import ProjectEulerSolutions.Lib.PandigitalConcat
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerStatements.Lib.ListMaximum

namespace data.«project-euler-statements».data.py.project_euler_statements.p38.naive
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P38 ProjectEulerSolutions.PandigitalConcat
set_option Elab.async false
private abbrev program := P38Ast.module
variable {globals : Mutable.Globals}
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number
private abbrev work (base : Mutable.Heap) (items : List Nat) (garbage : Mutable.Heap) :=
  ProjectEulerSolutions.HeapCollection.working base (numbers items) garbage

private abbrev innerBody : List Stmt :=
  [.assign [.name "value"] (.call (.name "concat_product") [.name "n", .name "k"]),
   .ifThen (.call (.name "is_pandigital") [.name "value", .name "width"])
     [.expr (.call (.attribute (.name "vals") "append") [.name "value"])] []]
private abbrev outerBody : List Stmt :=
  [.forIn (.name "k") (.call (.name "range") [.constant (.int 2), .binOp (.name "width") .add (.constant (.int 1))]) innerBody []]
private def selected (width n k : Nat) : List Nat := if accepted width n k then [concatProduct n k] else []
private def row (width n first count : Nat) : List Nat :=
  (List.range' first count).filterMap fun k => if accepted width n k then some (concatProduct n k) else none
private def rows (width first count : Nat) : List Nat := (List.range' first count).flatMap (seedValues width)

private theorem row_succ (width n first count : Nat) :
    row width n first (count + 1) = selected width n first ++ row width n (first + 1) count := by
  cases yes : accepted width n first <;> simp [row, selected, List.range'_succ, yes]

private structure Locals (env : HeapCalls.Env) (width n address : Nat) : Prop where
  size : env "width" = some (number width)
  seed : env "n" = some (number n)
  collector : env "vals" = some (.ref address)

private theorem append_value (base : Mutable.Heap) (before : List Nat) (garbage : Mutable.Heap)
    (value : Nat) (env : HeapCalls.Env) (getVals : env "vals" = some (.ref base.length))
    (getValue : env "value" = some (number value)) :
    BlockContinues (globals := globals) program env
      [.expr (.call (.attribute (.name "vals") "append") [.name "value"])] (work base before garbage)
      env (work base (before ++ [value]) garbage) := by
  apply BlockContinues.discard
  have appended := Evaluates.append (globals := globals) (module := program) (env := env)
    (base := .name "vals") (expression := .name "value") (value := number value)
    (old := numbers before) (current := numbers before)
    (Evaluates.lookup (heap := work base before garbage) getVals)
    (by simp [work, ProjectEulerSolutions.HeapCollection.working]) (Evaluates.lookup getValue)
    (by simp [work, ProjectEulerSolutions.HeapCollection.working])
  simpa [work, ProjectEulerSolutions.HeapCollection.working, numbers, List.set_append_right] using appended

private theorem collect_one (width n k : Nat) (two : 2 ≤ k) (base : Mutable.Heap) (before : List Nat)
    (garbage : Mutable.Heap) (env : HeapCalls.Env) (locals : Locals env width n base.length)
    (getK : env "k" = some (number k)) :
    ∃ finalEnv finalGarbage, Locals finalEnv width n base.length ∧
      BlockContinues (globals := globals) program env innerBody (work base before garbage)
        finalEnv (work base (before ++ selected width n k) finalGarbage) := by
  obtain ⟨concatGarbage, concatenated⟩ := concat_product.result (globals := globals) n k (work base before garbage)
  let updated := setLocal env "value" (number (concatProduct n k))
  obtain ⟨predicateGarbage, tested⟩ := is_pandigital.result (globals := globals) (concatProduct n k) width
    (work base before garbage ++ concatGarbage)
  have finalLocals : Locals updated width n base.length :=
    ⟨by simpa [updated, setLocal] using locals.size, by simpa [updated, setLocal] using locals.seed,
      by simpa [updated, setLocal] using locals.collector⟩
  have testedCall : Evaluates (globals := globals) program updated
      (.call (.name "is_pandigital") [.name "value", .name "width"])
      (work base before garbage ++ concatGarbage)
      (.scalar (.bool (accepted width n k)))
      ((work base before garbage ++ concatGarbage) ++ predicateGarbage) := by
    have evaluated := Evaluates.call (globals := globals) (env := updated)
      (.cons (Evaluates.lookup (name := "value") (by simp [updated, setLocal])) (.cons (Evaluates.lookup finalLocals.size) .nil)) tested
    simpa only [accepted, show decide (1 < k) = true from decide_eq_true (by omega), Bool.true_and] using evaluated
  have first : BlockContinues (globals := globals) program env [innerBody[0]'(by decide)] (work base before garbage)
      updated (work base before garbage ++ concatGarbage) :=
    BlockContinues.assign (Evaluates.call (.cons (Evaluates.lookup locals.seed) (.cons (Evaluates.lookup getK) .nil)) concatenated)
  let trash := (garbage ++ concatGarbage) ++ predicateGarbage
  cases yes : accepted width n k with
  | false =>
      refine ⟨updated, trash, finalLocals, ?_⟩
      have branch : BlockContinues (globals := globals) program updated [innerBody[1]'(by decide)]
          (work base before garbage ++ concatGarbage) updated (work base before trash) := by
        have executed := BlockContinues.branch (yes := [.expr (.call (.attribute (.name "vals") "append") [.name "value"])]) (flag := false) (by simpa only [yes] using testedCall) rfl .nil
        simpa only [work, ProjectEulerSolutions.HeapCollection.append, trash] using executed
      simpa [innerBody, selected, yes] using first.append branch
  | true =>
      refine ⟨updated, trash, finalLocals, ?_⟩
      have appended := append_value (globals := globals) base before trash (concatProduct n k) updated finalLocals.collector
        (by simp [updated, setLocal])
      have branch : BlockContinues (globals := globals) program updated [innerBody[1]'(by decide)]
          (work base before garbage ++ concatGarbage) updated (work base (before ++ [concatProduct n k]) trash) := by
        apply BlockContinues.branch (flag := true) (by simpa only [yes] using testedCall) rfl
        simpa only [work, ProjectEulerSolutions.HeapCollection.append, trash] using appended
      simpa [innerBody, selected, yes] using first.append branch

/-- Each product count is visited once, retaining all successful values and the collector's identity. -/
private theorem collect_inner (width n first count : Nat) (two : 2 ≤ first) (endpoint : first + count = width + 1)
    (base : Mutable.Heap) (before : List Nat) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (locals : Locals env width n base.length) :
    ∃ finalEnv finalGarbage, Locals finalEnv width n base.length ∧
      BlockContinues (globals := globals) program env [.rangeStepLoop "k" first (width + 1) 1 innerBody []]
        (work base before garbage) finalEnv (work base (before ++ row width n first count) finalGarbage) := by
  induction count generalizing first before garbage env with
  | zero =>
      refine ⟨env, garbage, locals, ?_⟩
      simpa [row] using BlockContinues.range_done (module := program) (env := env) (heap := work base before garbage)
        (by simp [Calls.rangeContinues]; omega) BlockContinues.nil
  | succ count ih =>
      let bound := setLocal env "k" (number first)
      have current : Locals bound width n base.length :=
        ⟨by simpa [bound, setLocal] using locals.size, by simpa [bound, setLocal] using locals.seed,
          by simpa [bound, setLocal] using locals.collector⟩
      obtain ⟨middleEnv, middleGarbage, nextLocals, collected⟩ := collect_one (globals := globals) width n first two base before garbage bound current (by simp [bound, setLocal])
      obtain ⟨finalEnv, finalGarbage, finalLocals, rest⟩ := ih (first + 1) (by omega) (by omega)
        (before ++ selected width n first) middleGarbage middleEnv nextLocals
      refine ⟨finalEnv, finalGarbage, finalLocals, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [Calls.loopContinuation, show Calls.loopControl innerBody = false from rfl,
        Bool.false_eq_true, if_false, row_succ, List.append_assoc, Int.natCast_add, Int.natCast_one] using collected.append rest

private theorem collect_outer (width first count : Nat) (nonempty : 0 < width) (endpoint : first + count = seedLimit width)
    (base : Mutable.Heap) (before : List Nat) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (getWidth : env "width" = some (number width)) (getVals : env "vals" = some (.ref base.length)) :
    ∃ finalEnv finalGarbage, finalEnv "width" = some (number width) ∧ finalEnv "vals" = some (.ref base.length) ∧
      BlockContinues (globals := globals) program env [.rangeStepLoop "n" first (seedLimit width) 1 outerBody []]
        (work base before garbage) finalEnv (work base (before ++ rows width first count) finalGarbage) := by
  induction count generalizing first before garbage env with
  | zero =>
      refine ⟨env, garbage, getWidth, getVals, ?_⟩
      simpa [rows] using BlockContinues.range_done (module := program) (env := env) (heap := work base before garbage)
        (by simp [Calls.rangeContinues]; omega) BlockContinues.nil
  | succ count ih =>
      let bound := setLocal env "n" (number first)
      have current : Locals bound width first base.length :=
        ⟨by simpa [bound, setLocal] using getWidth, by simp [bound, setLocal], by simpa [bound, setLocal] using getVals⟩
      obtain ⟨middleEnv, middleGarbage, nextLocals, collected⟩ := collect_inner (globals := globals) width first 2 (width - 1)
        (by decide) (by omega) base before garbage bound current
      have pass : BlockContinues (globals := globals) program bound outerBody (work base before garbage)
          middleEnv (work base (before ++ seedValues width first) middleGarbage) := by
        apply BlockContinues.for_range (values := [number 2, number (width + 1)])
          (.cons Evaluates.constant (.cons (Evaluates.binary (av := number width) (bv := number 1)
            (middle := work base before garbage) (afterRight := work base before garbage) (value := number (width + 1)) (finalHeap := work base before garbage)
            (Evaluates.lookup current.size) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])) .nil)) rfl
        exact collected
      obtain ⟨finalEnv, finalGarbage, finalWidth, finalVals, rest⟩ := ih (first + 1) (by omega)
        (before ++ seedValues width first) middleGarbage middleEnv nextLocals.size nextLocals.collector
      refine ⟨finalEnv, finalGarbage, finalWidth, finalVals, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [Calls.loopContinuation, show Calls.loopControl outerBody = false from rfl,
        Bool.false_eq_true, if_false, rows, List.range'_succ, List.flatMap_cons,
        List.append_assoc, Int.natCast_add, Int.natCast_one] using pass.append rest

private theorem maximum_result (heap : Mutable.Heap) (address : Nat) (items : List Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getVals : env "vals" = some (.ref address)) :
    Evaluates (globals := globals) program env
      (.ifExp (.name "vals") (.builtinCall .max [.name "vals"]) (.constant (.int 0)))
      heap (number (listMax items)) heap := by
  cases items with
  | nil =>
      apply Evaluates.conditional (flag := false) (Evaluates.lookup getVals) _ Evaluates.constant
      simp [Mutable.truth, found, numbers]
  | cons first rest =>
      have folded : (rest.map (fun n : Nat => (n : Int))).foldl max (first : Int) =
          ((rest.foldl max first : Nat) : Int) :=
        ProjectEulerStatements.ListMaximum.fold_map (fun n : Nat => (n : Int))
          (by intro a b; dsimp; omega) rest first
      have maximum : Calls.maximumFrom (.int first) (rest.map (fun n : Nat => Constant.int n)) =
          .ok (.int ((rest.foldl max first : Nat) : Int)) := by
        simpa only [List.map_map, Function.comp_def, folded] using
          ScalarSet.maximumFrom_ints (rest.map (fun n : Nat => (n : Int))) first
      apply Evaluates.conditional (flag := true) (Evaluates.lookup getVals)
      · simp [Mutable.truth, found, numbers]
      · apply Evaluates.builtin (.cons (Evaluates.lookup getVals) .nil)
        simp [primitive, Mutable.sequence, found, numbers, number, List.mapM_map,
          Function.comp_def, ScalarSet.maximum, scalarResult, List.mapM_pure, maximum, listMax]

/-- Empty target widths return before allocating a candidate collector. -/
theorem empty (width : Int) (small : width < 2) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "naive" [.scalar (.int width)] heap (.scalar (.int 0)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true)
    (Evaluates.compare (av := .scalar (.int width)) (bv := number 2)
      (value := .scalar (.bool true)) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, small])) rfl
  exact BlockReturns.return_value Evaluates.constant

/-- Widths requiring nondecimal digits also return before search. -/
theorem large (width : Int) (above : 9 < width) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "naive" [.scalar (.int width)] heap (.scalar (.int 0)) heap := by
  apply BlockReturns.function rfl rfl
  have input : (functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
      ((findFunctionIn program.body "naive").getD ([], [])).2 [.scalar (.int width)] globals) "width" =
      some (.scalar (.int width)) := by cases globals <;> rfl
  apply BlockReturns.branch (flag := false)
    (Evaluates.compare (av := .scalar (.int width)) (bv := number 2)
      (value := .scalar (.bool false)) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup input) Evaluates.constant (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)) rfl
  apply BlockReturns.branch (flag := true)
    (Evaluates.compare (av := .scalar (.int width)) (bv := number 9)
      (value := .scalar (.bool true)) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup input) Evaluates.constant (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, above])) rfl
  exact BlockReturns.return_value Evaluates.constant

private theorem active (width : Nat) (two : 2 ≤ width) (decimal : width ≤ 9) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue (globals := globals) program "naive" [number width] heap
      (number (reference width)) finalHeap := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number width] globals
  have input : initial "width" = some (number width) := by cases globals <;> rfl
  let ready := setLocal initial "vals" (.ref heap.length)
  have getWidth : ready "width" = some (number width) := by simpa [ready, setLocal] using input
  have positive : 0 < seedLimit width := by unfold seedLimit; positivity
  obtain ⟨finalEnv, finalGarbage, finalWidth, finalVals, collected⟩ := collect_outer (globals := globals)
    width 1 (seedLimit width - 1) (by omega) (by omega) heap [] [] ready getWidth (by simp [ready, setLocal])
  let finalHeap := work heap (candidates width) finalGarbage
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := false)
    (Evaluates.compare (av := number width) (bv := number 2) (value := .scalar (.bool false))
      (middle := heap) (afterRight := heap) (finalHeap := heap) (Evaluates.lookup input) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)) rfl
  apply BlockReturns.branch (flag := false)
    (Evaluates.compare (av := number width) (bv := number 9) (value := .scalar (.bool false))
      (middle := heap) (afterRight := heap) (finalHeap := heap) (Evaluates.lookup input) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)) rfl
  apply BlockReturns.assign (value := .ref heap.length) (middle := work heap [] [])
    (Evaluates.list .nil)
  have searched : BlockContinues (globals := globals) program ready
      [.forIn (.name "n") (.call (.name "range") [.constant (.int 1),
        .binOp (.constant (.int 10)) .pow (.binOp (.name "width") .floorDiv (.constant (.int 2)))]) outerBody []]
      (work heap [] []) finalEnv finalHeap := by
    apply BlockContinues.for_range (values := [number 1, number (seedLimit width)])
      (middle := work heap [] [])
    · refine .cons Evaluates.constant (.cons ?_ .nil)
      apply Evaluates.binary (av := number 10) (bv := number (width / 2)) (middle := work heap [] [])
        (afterRight := work heap [] []) Evaluates.constant
      · exact Evaluates.binary (av := number width) (bv := number 2) (middle := work heap [] [])
          (afterRight := work heap [] []) (Evaluates.lookup getWidth) Evaluates.constant
          (by simp [Mutable.binary, scalarBinary, number])
      · have nonnegative : ¬ (width : Int) / 2 < 0 := not_lt_of_ge (Int.ediv_nonneg (by omega) (by omega))
        simp [Mutable.binary, scalarBinary, number, seedLimit, nonnegative]
        rfl
    · rfl
    · simpa only [rows, candidates, List.nil_append] using collected
  apply searched.returns
  apply BlockReturns.return_value
  have maximum := maximum_result (globals := globals) finalHeap heap.length (candidates width)
    (by simp [finalHeap, ProjectEulerSolutions.HeapCollection.working]) finalEnv finalVals
  simpa only [listMax] using maximum

/-- The complete reference executes for every natural target width. -/
theorem result (width : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue (globals := globals) program "naive" [number width] heap
      (number (reference width)) finalHeap := by
  by_cases small : width < 2
  · exact ⟨heap, by simpa only [reference_small width small] using empty (globals := globals) width (by omega) heap⟩
  · by_cases above : 9 < width
    · exact ⟨heap, by simpa only [reference_large width above] using large (globals := globals) width (by omega) heap⟩
    · exact active width (by omega) (by omega) heap

end data.«project-euler-statements».data.py.project_euler_statements.p38.naive
