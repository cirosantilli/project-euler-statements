import data.«project-euler-statements».data.py.project_euler_statements.«p61.table.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
open extend (numbers)
open PolygonalCycleSearch (remainingTypes)
private abbrev program := P61Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)

def rangeExpressions : List Expr :=
  [.constant (.int 4), .binOp (.name "max_sides") .add (.constant (.int 1))]
def typesExpression : Expr :=
  .listComp (.name "$formalsw.range.item")
    [("$formalsw.range.item", .call (.name "range") rangeExpressions, [])]
def startArguments : List Expr :=
  [.list [.name "start"], typesExpression, .name "__formalsw_cell_naive_families"]
def startCall : Expr := .call (.name "__formalsw_local_naive_extend") startArguments

def startValue (maxSides : Int) (start : Int) : Int :=
  PolygonalCycleSearch.fullScan PolygonalFamilies.family (remainingTypes maxSides).length [start]
    (remainingTypes maxSides)

def argumentHeap (heap : Mutable.Heap) (start maxSides : Int) (extra : Mutable.Heap) : Mutable.Heap :=
  heap ++ [.list [number start], .list (numbers (remainingTypes maxSides))] ++ extra

theorem remaining_nat (maxSides : Nat) :
    remainingTypes maxSides = (List.range' 4 (maxSides - 3)).map (fun (kind : Nat) => (kind : Int)) := by
  unfold remainingTypes
  have shifted : ((maxSides : Int) - 3).toNat = maxSides - 3 := by omega
  rw [shifted]

theorem remaining_valid (maxSides : Nat) (large : 3 ≤ maxSides) :
    ∀ kind ∈ remainingTypes maxSides, 3 ≤ kind ∧ kind ≤ maxSides := by
  intro kind member
  simp only [remaining_nat, List.mem_map] at member
  obtain ⟨index, inRange, equal⟩ := member
  have bound := List.mem_range'_1.mp inRange
  omega

theorem arguments_evaluate (maxSides : Nat) (large : 3 ≤ maxSides) (heap : Mutable.Heap)
    (start : Int) (familiesCell : Nat) (env : HeapCalls.Env)
    (getStart : env "start" = some (number start))
    (getMax : env "max_sides" = some (number maxSides))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (globals : Mutable.Globals := []) :
    ∃ extra, Evaluates.Arguments program env startArguments heap
      [.ref heap.length, .ref (heap.length + 1), .ref familiesCell]
      (argumentHeap heap start maxSides extra) globals := by
  let afterPath := heap ++ [.list [number start]]
  have path : Evaluates program env (.list [.name "start"]) heap (.ref heap.length) afterPath globals :=
    Evaluates.list (.cons (Evaluates.lookup getStart) .nil)
  obtain ⟨extra, typed⟩ := HeapCollection.range_map (globals := globals) program "$formalsw.range.item"
    (.name "$formalsw.range.item") (fun (n : Nat) => number n)
    (fun heap env n found => ⟨[], by simpa using
      (Evaluates.lookup (module := program) (heap := heap) (globals := globals) found)⟩)
    afterPath env rangeExpressions [number 4, number (maxSides + 1)] 4 (maxSides - 3)
    (.cons Evaluates.constant (.cons (Evaluates.binary (av := number maxSides) (bv := number 1)
      (middle := afterPath) (afterRight := afterPath) (finalHeap := afterPath)
      (Evaluates.lookup getMax) Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil))
    (by change Except.ok (ε := ExceptionObject) ((4 : Int), ((maxSides + 1 : Nat) : Int), (1 : Int)) =
          .ok (4, (4 : Int) + ((maxSides - 3 : Nat) : Int), 1)
        have endpoint : ((maxSides + 1 : Nat) : Int) = (4 : Int) + ((maxSides - 3 : Nat) : Int) := by omega
        rw [endpoint])
  refine ⟨extra, .cons path (.cons ?_ (.cons (Evaluates.lookup getCell) .nil))⟩
  simpa only [typesExpression, argumentHeap, afterPath, HeapCollection.working, numbers,
    remaining_nat, List.map_map, Function.comp_def,
    List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using typed

theorem start_evaluate (maxSides : Nat) (large : 3 ≤ maxSides)
    (world : extend.World heap familiesCell maxSides) (start : Int) (env : HeapCalls.Env)
    (getStart : env "start" = some (number start))
    (getMax : env "max_sides" = some (number maxSides))
    (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (globals : Mutable.Globals := []) :
    ∃ extra, Evaluates program env startCall heap (number (startValue maxSides start)) (heap ++ extra) globals := by
  obtain ⟨allocated, arguments⟩ := arguments_evaluate maxSides large heap start familiesCell env
    getStart getMax getCell globals
  let extra := [.list [number start], .list (numbers (remainingTypes maxSides))] ++ allocated
  have state : extend.SearchState (argumentHeap heap start maxSides allocated) heap.length (heap.length + 1)
      familiesCell maxSides [start] (remainingTypes maxSides) := by
    refine {
      world := by simpa only [argumentHeap, extra, List.append_assoc] using world.append extra
      pathFound := ?_
      remainingFound := ?_
      validKinds := remaining_valid maxSides large
    }
    · simp [argumentHeap, numbers]
    · simp [argumentHeap, extend.kinds, numbers]
  obtain ⟨searched, returned⟩ := extend.search_result (remainingTypes maxSides).length
    (argumentHeap heap start maxSides allocated) heap.length (heap.length + 1) familiesCell maxSides
    [start] (remainingTypes maxSides) state (by simp) (by rfl) globals
  refine ⟨extra ++ searched, ?_⟩
  simpa only [startCall, startValue, extra, argumentHeap, List.append_assoc] using Evaluates.call arguments returned

def startIterable : Expr := .subscript
  (.subscript (.name "__formalsw_cell_naive_families") (.constant (.int 0))) (.constant (.int 3))
def startBody : List Stmt := [.assign [.name "best"] (.builtinCall .max [.name "best", startCall])]

theorem iterable_evaluate (world : extend.World heap familiesCell maxSides) (large : 3 ≤ maxSides)
    (env : HeapCalls.Env) (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (globals : Mutable.Globals := []) :
    Evaluates program env startIterable heap (.ref (world.target 3)) heap globals := by
  have table : Evaluates program env
      (.subscript (.name "__formalsw_cell_naive_families") (.constant (.int 0))) heap (.ref world.table) heap globals := by
    apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getCell) Evaluates.constant
    exact Mutable.getItem_list _ _ 0 [.ref world.table] world.cellFound (by simp)
  apply Evaluates.subscript (middle := heap) (afterIndex := heap) (finalHeap := heap)
    (by intros; intro impossible; cases impossible) table Evaluates.constant
  exact Mutable.getItem_dictionary heap world.table world.entries world.tableFound (.int 3)
    (world.looked 3 ⟨by decide, large⟩)

theorem start_loop (maxSides : Nat) (large : 3 ≤ maxSides) (world : extend.World heap familiesCell maxSides)
    (env : HeapCalls.Env) (getCell : env "__formalsw_cell_naive_families" = some (.ref familiesCell))
    (getMax : env "max_sides" = some (number maxSides))
    (best : Int) (getBest : env "best" = some (number best)) (globals : Mutable.Globals := []) :
    ∃ extra finalEnv, BlockContinues program env [.forIn (.name "start") startIterable startBody []]
        heap finalEnv (heap ++ extra) globals ∧
      finalEnv "best" = some (number ((PolygonalFamilies.family 3).foldl
        (fun best start => max best (startValue maxSides start)) best)) := by
  let invariant := fun (currentHeap : Mutable.Heap) (currentEnv : HeapCalls.Env) (currentBest : Int) =>
    Nonempty (extend.World currentHeap familiesCell maxSides) ∧
      currentEnv "__formalsw_cell_naive_families" = some (.ref familiesCell) ∧
      currentEnv "max_sides" = some (number maxSides) ∧ currentEnv "best" = some (number currentBest)
  have bindInvariant : ∀ currentHeap currentEnv currentBest start, invariant currentHeap currentEnv currentBest →
      start ∈ PolygonalFamilies.family 3 →
      invariant currentHeap (setLocal currentEnv "start" (number start)) currentBest := by
    intro currentHeap currentEnv currentBest start good _
    exact ⟨good.1, by simpa [setLocal] using good.2.1,
      by simpa [setLocal] using good.2.2.1, by simpa [setLocal] using good.2.2.2⟩
  have cell : ∀ currentHeap currentEnv currentBest start, invariant currentHeap currentEnv currentBest →
      start ∈ PolygonalFamilies.family 3 → currentEnv "start" = some (number start) →
      ∃ finalEnv finalHeap, BlockContinues program currentEnv startBody currentHeap finalEnv finalHeap globals ∧
        invariant finalHeap finalEnv (max currentBest (startValue maxSides start)) ∧
        (∃ extra, finalHeap = currentHeap ++ extra) ∧ HeapRangeFold.Frame ["start", "best"] currentEnv finalEnv := by
    intro currentHeap currentEnv currentBest start good _ getStart
    obtain ⟨⟨current⟩, currentCell, currentMax, currentBestFound⟩ := good
    obtain ⟨extra, evaluated⟩ := start_evaluate maxSides large current start currentEnv getStart currentMax currentCell globals
    have maximum : Evaluates program currentEnv (.builtinCall .max [.name "best", startCall]) currentHeap
        (number (max currentBest (startValue maxSides start))) (currentHeap ++ extra) globals := by
      apply Evaluates.builtin (.cons (Evaluates.lookup currentBestFound) (.cons evaluated .nil))
      by_cases better : currentBest < startValue maxSides start
      · simp [primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp, scalarResult,
          better, Int.max_eq_right (by omega : currentBest ≤ startValue maxSides start)]
      · simp [primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare, evalCmpOp, scalarResult,
          better, Int.max_eq_left (by omega : startValue maxSides start ≤ currentBest)]
    refine ⟨setLocal currentEnv "best" (number (max currentBest (startValue maxSides start))), currentHeap ++ extra,
      BlockContinues.assign maximum, ⟨⟨current.append extra⟩, ?_, ?_, rfl⟩, ⟨extra, rfl⟩,
      HeapRangeFold.Frame.updated _ currentEnv "best" _ (by decide)⟩
    · simpa [setLocal] using currentCell
    · simpa [setLocal] using currentMax
  obtain ⟨finalEnv, finalHeap, executed, good, ⟨extra, layout⟩, _⟩ := HeapSequenceFold.for_list program "start" startBody rfl
    ["start", "best"] (by decide) number (fun best start => max best (startValue maxSides start)) invariant
    (world.target 3) (PolygonalFamilies.family 3) bindInvariant cell heap env best
    ⟨⟨world⟩, getCell, getMax, getBest⟩ startIterable (by intro expressions impossible; cases impossible)
    (iterable_evaluate world (by omega) env getCell globals) (world.familyFound 3 ⟨by decide, by omega⟩)
  rw [layout] at executed
  exact ⟨extra, finalEnv, executed, good.2.2.2⟩

end data.«project-euler-statements».data.py.project_euler_statements.p61.naive
