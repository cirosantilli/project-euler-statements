import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p11.py.ast»
import FormalSW
import ProjectEulerStatements.Lib.GridProducts

namespace data.«project-euler-statements».data.py.project_euler_statements.p11
open FormalSW.PyAst
private abbrev program := P11Ast.module

private def bounded (index length : Expr) : Expr :=
  .compare (.constant (.int 0)) [(.ltE, index), (.lt, length)]

private theorem bounded.result (env : HeapCalls.Env) (heap : Mutable.Heap)
    (index length : Expr) (value : Int) (size : Nat)
    (getIndex : HeapCalls.Evaluates program env index heap (.scalar (.int value)) heap)
    (getLength : HeapCalls.Evaluates program env length heap (.scalar (.int size)) heap) :
    HeapCalls.Evaluates program env (bounded index length) heap
      (.scalar (.bool (decide (0 ≤ value ∧ value < size)))) heap := by
  by_cases nonnegative : 0 ≤ value
  · simp only [nonnegative, true_and]
    apply HeapCalls.Evaluates.chain HeapCalls.Evaluates.constant
    apply HeapCalls.Evaluates.Compares.next (compared := .scalar (.bool true)) (afterComparison := heap) getIndex
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, nonnegative]
    · rfl
    · exact HeapCalls.Evaluates.Compares.last getLength (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  · simp only [nonnegative, false_and, decide_false]
    apply HeapCalls.Evaluates.chain HeapCalls.Evaluates.constant
    exact HeapCalls.Evaluates.Compares.stop getIndex
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, nonnegative]) rfl

private abbrev rowExpression : Expr := .subscript (.name "grid") (.name "r")
private abbrev condition : Expr := .boolOp .and [
  bounded (.name "r") (.builtinCall .len [.name "grid"]),
  bounded (.name "c") (.builtinCall .len [rowExpression])]
private def gridBody : List Stmt :=
  match findFunctionIn program.body "grid_val" with
  | some (_, body) => executableBody body
  | none => []

private theorem grid_val.block (heap : Mutable.Heap) (address : Nat) (rows : List Nat)
    (found : heap[address]? = some (.list (rows.map Mutable.Value.ref)))
    (types : ∀ row ∈ rows, Mutable.Value.HasType heap (.ref row) "list[int]")
    (env : HeapCalls.Env) (r c : Int)
    (getGrid : env "grid" = some (.ref address))
    (getRow : env "r" = some (.scalar (.int r)))
    (getColumn : env "c" = some (.scalar (.int c))) :
    ∃ answer : Int, HeapCalls.BlockReturns program env gridBody heap (.scalar (.int answer)) heap := by
  have rowGuard := bounded.result env heap (.name "r") (.builtinCall .len [.name "grid"]) r rows.length
    (HeapCalls.Evaluates.lookup getRow)
    (HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup getGrid) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, found]))
  by_cases rowValid : 0 ≤ r ∧ r < rows.length
  · have rowIndex : r.toNat < rows.length := by omega
    let row := rows[r.toNat]
    obtain ⟨values, contents⟩ := Mutable.Value.ints_of_hasType (types row (List.getElem_mem rowIndex))
    have readRow : HeapCalls.Evaluates program env rowExpression heap (.ref row) heap := by
      apply HeapCalls.Evaluates.subscript (by intros a b c impossible; cases impossible)
        (HeapCalls.Evaluates.lookup getGrid) (HeapCalls.Evaluates.lookup getRow)
      have read := Mutable.getItem_list heap address r.toNat (rows.map Mutable.Value.ref) found (by simpa using rowIndex)
      rw [List.getElem_map] at read
      simpa [Int.toNat_of_nonneg rowValid.1, row] using read
    have columnGuard := bounded.result env heap (.name "c") (.builtinCall .len [rowExpression]) c values.length
      (HeapCalls.Evaluates.lookup getColumn)
      (HeapCalls.Evaluates.builtin (.cons readRow .nil) (by simp [HeapCalls.primitive, Mutable.length, contents]))
    have wholeGuard : HeapCalls.Evaluates program env condition heap
        (.scalar (.bool (decide (0 ≤ c ∧ c < values.length)))) heap := by
      apply HeapCalls.Evaluates.boolean_next (flag := true)
        (value := .scalar (.bool true)) (middle := heap)
      · simpa [rowValid] using rowGuard
      · rfl
      · rfl
      · exact HeapCalls.Evaluates.boolean_last columnGuard rfl
    by_cases columnValid : 0 ≤ c ∧ c < values.length
    · have columnIndex : c.toNat < values.length := by omega
      refine ⟨values[c.toNat], ?_⟩
      apply HeapCalls.BlockReturns.return_value
      apply HeapCalls.Evaluates.conditional (flag := true)
        (value := .scalar (.bool true)) (middle := heap)
      · simpa [columnValid] using wholeGuard
      · rfl
      · apply HeapCalls.Evaluates.subscript (by intros a b c impossible; cases impossible)
          readRow (HeapCalls.Evaluates.lookup getColumn)
        have read := Mutable.getItem_list heap row c.toNat (values.map (fun n => .scalar (.int n))) contents
          (by simpa using columnIndex)
        rw [List.getElem_map] at read
        simpa [Int.toNat_of_nonneg columnValid.1] using read
    · refine ⟨0, ?_⟩
      apply HeapCalls.BlockReturns.return_value
      exact HeapCalls.Evaluates.conditional (flag := false)
        (by simpa [columnValid] using wholeGuard) rfl HeapCalls.Evaluates.constant
  · refine ⟨0, ?_⟩
    apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.conditional (flag := false) (value := .scalar (.bool false)) (middle := heap)
    · exact HeapCalls.Evaluates.boolean_stop (flag := false) (by simpa [rowValid] using rowGuard) rfl rfl
    · rfl
    · exact HeapCalls.Evaluates.constant

theorem grid_val.result (heap : Mutable.Heap) (address : Nat) (r c : Int)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    ∃ answer : Int, HeapCalls.ReturnsValue program "grid_val"
      [.ref address, .scalar (.int r), .scalar (.int c)] heap (.scalar (.int answer)) heap := by
  obtain ⟨rows, found, types⟩ := Mutable.Value.lists_of_hasType typed
  obtain ⟨answer, executed⟩ := grid_val.block heap address rows found types
    (HeapCalls.argumentEnv
      [⟨"grid", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩,
        ⟨"r", some (.name "int"), none⟩, ⟨"c", some (.name "int"), none⟩]
      [.ref address, .scalar (.int r), .scalar (.int c)]) r c rfl rfl rfl
  exact ⟨answer, HeapCalls.BlockReturns.function rfl rfl executed⟩

theorem grid_val.«Returns» (heap : Mutable.Heap) (address : Nat) (r c : Int) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "grid_val" [.ref address, .scalar (.int r), .scalar (.int c)] heap).Returns := by
  obtain ⟨answer, executed⟩ := grid_val.result heap address r c typed
  exact executed.returns

theorem grid_val.«Supported» (heap : Mutable.Heap) (address : Nat) (r c : Int) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "grid_val" [.ref address, .scalar (.int r), .scalar (.int c)] heap).Supported :=
  (grid_val.«Returns» heap address r c valid typed).supported

open ProjectEulerStatements.Grid (Direction)

private def productName : Direction → String
  | .right => "prod_right_n"
  | .down => "prod_down_n"
  | .downRight => "prod_diag_right_n"
  | .downLeft => "prod_diag_left_n"

private def productRow : Direction → Expr
  | .right => .name "r"
  | _ => .binOp (.name "r") .add (.name "i")

private def productColumn : Direction → Expr
  | .down => .name "c"
  | .downLeft => .binOp (.name "c") .sub (.name "i")
  | _ => .binOp (.name "c") .add (.name "i")

private def productBody (direction : Direction) : List Stmt :=
  [.augAssign (.name "acc") .mult (.call (.name "grid_val")
    [.name "grid", productRow direction, productColumn direction])]

private theorem offsets.result (direction : Direction) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (r c : Int) (position : Nat)
    (getRow : env "r" = some (.scalar (.int r)))
    (getColumn : env "c" = some (.scalar (.int c)))
    (getIndex : env "i" = some (.scalar (.int position))) :
    HeapCalls.Evaluates program env (productRow direction) heap (.scalar (.int (direction.row r position))) heap ∧
    HeapCalls.Evaluates program env (productColumn direction) heap (.scalar (.int (direction.column c position))) heap := by
  cases direction <;> constructor
  all_goals first
    | exact HeapCalls.Evaluates.lookup getRow
    | exact HeapCalls.Evaluates.lookup getColumn
    | exact HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getRow) (HeapCalls.Evaluates.lookup getIndex) rfl
    | exact HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getColumn) (HeapCalls.Evaluates.lookup getIndex) rfl

private theorem product.loop (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (r c n : Int) (position : Nat) (bounded : position ≤ n.toNat)
    (env : HeapCalls.Env) (acc : Int)
    (getGrid : env "grid" = some (.ref address))
    (getRow : env "r" = some (.scalar (.int r)))
    (getColumn : env "c" = some (.scalar (.int c)))
    (getAcc : env "acc" = some (.scalar (.int acc))) :
    ∃ finalEnv answer, HeapCalls.BlockContinues program env
      [.rangeStepLoop "i" position n 1 (productBody direction) []] heap finalEnv heap ∧
      finalEnv "acc" = some (.scalar (.int answer)) := by
  by_cases active : (position : Int) < n
  · let indexed := HeapCalls.setLocal env "i" (.scalar (.int position))
    have savedGrid : indexed "grid" = some (.ref address) := by simpa [indexed, HeapCalls.setLocal] using getGrid
    have savedRow : indexed "r" = some (.scalar (.int r)) := by simpa [indexed, HeapCalls.setLocal] using getRow
    have savedColumn : indexed "c" = some (.scalar (.int c)) := by simpa [indexed, HeapCalls.setLocal] using getColumn
    have savedAcc : indexed "acc" = some (.scalar (.int acc)) := by simpa [indexed, HeapCalls.setLocal] using getAcc
    obtain ⟨row, column⟩ := offsets.result direction indexed heap r c position savedRow savedColumn rfl
    obtain ⟨value, evaluated⟩ := grid_val.result heap address (direction.row r position)
      (direction.column c position) typed
    let nextEnv := HeapCalls.setLocal indexed "acc" (.scalar (.int (acc * value)))
    have step : HeapCalls.BlockContinues program indexed (productBody direction) heap nextEnv heap := by
      apply HeapCalls.BlockContinues.augAssign savedAcc
        (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup savedGrid) (.cons row (.cons column .nil))) evaluated)
      rfl
    obtain ⟨finalEnv, answer, rest, result⟩ := product.loop direction heap address typed r c n
      (position + 1) (by omega) nextEnv (acc * value)
      (by simpa [nextEnv, HeapCalls.setLocal] using savedGrid)
      (by simpa [nextEnv, HeapCalls.setLocal] using savedRow)
      (by simpa [nextEnv, HeapCalls.setLocal] using savedColumn) rfl
    refine ⟨finalEnv, answer, ?_, result⟩
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
    simpa only [Nat.cast_add, Nat.cast_one] using step.append rest
  · refine ⟨env, acc, ?_, getAcc⟩
    exact HeapCalls.BlockContinues.range_done (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil
termination_by n.toNat - position
decreasing_by omega

private abbrev productArgs : List Arg :=
  [⟨"grid", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩,
    ⟨"r", some (.name "int"), none⟩, ⟨"c", some (.name "int"), none⟩, ⟨"n", some (.name "int"), none⟩]

theorem product.result (direction : Direction) (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    ∃ answer : Int, HeapCalls.ReturnsValue program (productName direction)
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap (.scalar (.int answer)) heap := by
  let initialEnv := HeapCalls.setLocal (HeapCalls.argumentEnv productArgs
    [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)]) "acc" (.scalar (.int 1))
  obtain ⟨finalEnv, answer, loop, result⟩ := product.loop direction heap address typed r c n 0
    (by omega) initialEnv 1 rfl rfl rfl rfl
  refine ⟨answer, ?_⟩
  apply HeapCalls.BlockReturns.function (args := productArgs)
    (body := [.expr (.constant (.string "\n    @formalsw: Returns\n    ")),
      .assign [.name "acc"] (.constant (.int 1)),
      .forIn (.name "i") (.call (.name "range") [.name "n"]) (productBody direction) [],
      .return (.name "acc")])
    (by cases direction <;> rfl) rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockContinues.returns
    (HeapCalls.BlockContinues.for_range (.cons (HeapCalls.Evaluates.lookup (name := "n") rfl) .nil) rfl loop)
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup result)

private theorem product.returns (direction : Direction) (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program (productName direction)
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Returns := by
  obtain ⟨answer, executed⟩ := product.result direction heap address r c n typed
  exact executed.returns

theorem prod_right_n.«Returns» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_right_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Returns :=
  product.returns .right heap address r c n valid typed
theorem prod_down_n.«Returns» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_down_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Returns :=
  product.returns .down heap address r c n valid typed
theorem prod_diag_right_n.«Returns» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_diag_right_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Returns :=
  product.returns .downRight heap address r c n valid typed
theorem prod_diag_left_n.«Returns» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_diag_left_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Returns :=
  product.returns .downLeft heap address r c n valid typed

private theorem product.supported (direction : Direction) (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program (productName direction)
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Supported :=
  (product.returns direction heap address r c n valid typed).supported

theorem prod_right_n.«Supported» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_right_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Supported :=
  product.supported .right heap address r c n valid typed
theorem prod_down_n.«Supported» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_down_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Supported :=
  product.supported .down heap address r c n valid typed
theorem prod_diag_right_n.«Supported» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_diag_right_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Supported :=
  product.supported .downRight heap address r c n valid typed
theorem prod_diag_left_n.«Supported» (heap : Mutable.Heap) (address : Nat) (r c n : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "prod_diag_left_n"
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap).Supported :=
  product.supported .downLeft heap address r c n valid typed

private abbrev integers (items : List Int) : List Mutable.Value :=
  items.map (fun value => .scalar (.int value))

private def collectionBound (full : Bool) : Expr :=
  if full then .constant (.int 20) else .binOp (.constant (.int 21)) .sub (.name "n")

private def collectionStop (full : Bool) (n : Int) : Int := if full then 20 else 21 - n

private theorem collectionBound.result (full : Bool) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (n : Int) (getN : env "n" = some (.scalar (.int n))) :
    HeapCalls.Evaluates program env (collectionBound full) heap (.scalar (.int (collectionStop full n))) heap := by
  cases full
  · exact HeapCalls.Evaluates.binary HeapCalls.Evaluates.constant (HeapCalls.Evaluates.lookup getN) rfl
  · exact HeapCalls.Evaluates.constant

private def collectionColumn : Direction → Expr
  | .downLeft => .binOp (.binOp (.name "c") .add (.name "n")) .sub (.constant (.int 1))
  | _ => .name "c"

private def collectionElement (direction : Direction) : Expr :=
  .call (.name (productName direction)) [.name "grid", .name "r", collectionColumn direction, .name "n"]

private theorem collectionElement.result (direction : Direction) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (address : Nat) (r c n : Int) (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (getGrid : env "grid" = some (.ref address)) (getR : env "r" = some (.scalar (.int r)))
    (getC : env "c" = some (.scalar (.int c))) (getN : env "n" = some (.scalar (.int n))) :
    ∃ answer : Int, HeapCalls.Evaluates program env (collectionElement direction) heap (.scalar (.int answer)) heap := by
  let column := if direction = .downLeft then c + n - 1 else c
  have readColumn : HeapCalls.Evaluates program env (collectionColumn direction) heap (.scalar (.int column)) heap := by
    cases direction
    all_goals first
      | exact HeapCalls.Evaluates.lookup getC
      | exact HeapCalls.Evaluates.binary
          (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getC) (HeapCalls.Evaluates.lookup getN) rfl)
          HeapCalls.Evaluates.constant rfl
  obtain ⟨answer, called⟩ := product.result direction heap address r column n typed
  exact ⟨answer, HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup getGrid)
    (.cons (HeapCalls.Evaluates.lookup getR) (.cons readColumn (.cons (HeapCalls.Evaluates.lookup getN) .nil)))) called⟩

private abbrev collectionInner (direction : Direction) (address : Nat) : List Stmt :=
  [.comprehensionAppend address (collectionElement direction)]

private theorem collection.inner (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (items : List Int) (position : Nat) (r n stop : Int) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getR : env "r" = some (.scalar (.int r)))
    (getN : env "n" = some (.scalar (.int n))) :
    ∃ finalEnv finalItems, HeapCalls.BlockContinues program env
      [.rangeStepLoop "c" position stop 1 (collectionInner direction heap.length) []]
      (heap ++ [.list (integers items)]) finalEnv (heap ++ [.list (integers finalItems)]) ∧
      finalEnv "grid" = some (.ref address) ∧ finalEnv "n" = some (.scalar (.int n)) := by
  by_cases active : (position : Int) < stop
  · let boundEnv := HeapCalls.setLocal env "c" (.scalar (.int position))
    have grid : boundEnv "grid" = some (.ref address) := by simpa [boundEnv, HeapCalls.setLocal] using getGrid
    have row : boundEnv "r" = some (.scalar (.int r)) := by simpa [boundEnv, HeapCalls.setLocal] using getR
    have count : boundEnv "n" = some (.scalar (.int n)) := by simpa [boundEnv, HeapCalls.setLocal] using getN
    obtain ⟨answer, element⟩ := collectionElement.result direction boundEnv _ address r position n
      (typed.append _) grid row rfl count
    have emitted : HeapCalls.BlockContinues program boundEnv (collectionInner direction heap.length)
        (heap ++ [.list (integers items)]) boundEnv (heap ++ [.list (integers (items ++ [answer]))]) := by
      have write := HeapCalls.BlockContinues.comprehension_append (address := heap.length) element
        (by simp : (heap ++ [.list (integers items)])[heap.length]? = some (.list (integers items)))
      simpa [collectionInner, integers, List.map_append] using write
    obtain ⟨finalEnv, finalItems, rest, grid, count⟩ := collection.inner direction heap address typed
      (items ++ [answer]) (position + 1) r n stop boundEnv grid row count
    refine ⟨finalEnv, finalItems, ?_, grid, count⟩
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
    simpa [collectionInner, Calls.loopContinuation, Calls.loopControl, Nat.cast_add, Nat.cast_one]
      using emitted.append rest
  · exact ⟨env, items, HeapCalls.BlockContinues.range_done
      (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil, getGrid, getN⟩
termination_by stop.toNat - position
decreasing_by omega

private abbrev collectionOuter (direction : Direction) (address : Nat) : List Stmt :=
  [.forIn (.name "c") (.call (.name "range") [collectionBound (direction == .down)])
    (collectionInner direction address) []]

private theorem collection.outer (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (items : List Int) (position : Nat) (n stop : Int) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getN : env "n" = some (.scalar (.int n))) :
    ∃ finalEnv finalItems, HeapCalls.BlockContinues program env
      [.rangeStepLoop "r" position stop 1 (collectionOuter direction heap.length) []]
      (heap ++ [.list (integers items)]) finalEnv (heap ++ [.list (integers finalItems)]) ∧
      finalEnv "grid" = some (.ref address) ∧ finalEnv "n" = some (.scalar (.int n)) := by
  by_cases active : (position : Int) < stop
  · let boundEnv := HeapCalls.setLocal env "r" (.scalar (.int position))
    have grid : boundEnv "grid" = some (.ref address) := by simpa [boundEnv, HeapCalls.setLocal] using getGrid
    have count : boundEnv "n" = some (.scalar (.int n)) := by simpa [boundEnv, HeapCalls.setLocal] using getN
    obtain ⟨middleEnv, middleItems, inner, grid, count⟩ := collection.inner direction heap address typed
      items 0 position n (collectionStop (direction == .down) n) boundEnv grid rfl count
    have entered : HeapCalls.BlockContinues program boundEnv (collectionOuter direction heap.length)
        (heap ++ [.list (integers items)]) middleEnv (heap ++ [.list (integers middleItems)]) :=
      HeapCalls.BlockContinues.for_range
        (.cons (collectionBound.result _ boundEnv _ n (by simpa [boundEnv, HeapCalls.setLocal] using getN)) .nil)
        rfl inner
    obtain ⟨finalEnv, finalItems, rest, grid, count⟩ := collection.outer direction heap address typed
      middleItems (position + 1) n stop middleEnv grid count
    refine ⟨finalEnv, finalItems, ?_, grid, count⟩
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
    simpa [collectionOuter, Calls.loopContinuation, Calls.loopControl, Nat.cast_add, Nat.cast_one]
      using entered.append rest
  · exact ⟨env, items, HeapCalls.BlockContinues.range_done
      (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil, getGrid, getN⟩
termination_by stop.toNat - position
decreasing_by omega

private def collection (direction : Direction) : Expr :=
  .listComp (collectionElement direction)
    [("r", .call (.name "range") [collectionBound (direction == .right)], []),
     ("c", .call (.name "range") [collectionBound (direction == .down)], [])]

private theorem collection.result (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") (n : Int) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getN : env "n" = some (.scalar (.int n))) :
    ∃ items, HeapCalls.Evaluates program env (collection direction) heap (.ref heap.length)
      (heap ++ [.list (integers items)]) := by
  let localEnv := HeapCalls.comprehensionEnv env
    [("r", .call (.name "range") [collectionBound (direction == .right)], []),
     ("c", .call (.name "range") [collectionBound (direction == .down)], [])]
  have grid : localEnv "grid" = some (.ref address) := by simpa [localEnv, HeapCalls.comprehensionEnv] using getGrid
  have count : localEnv "n" = some (.scalar (.int n)) := by simpa [localEnv, HeapCalls.comprehensionEnv] using getN
  obtain ⟨finalEnv, items, loop, _, _⟩ := collection.outer direction heap address typed [] 0 n
    (collectionStop (direction == .right) n) localEnv grid count
  exact ⟨items, HeapCalls.Evaluates.list_comp_range
    (.cons (collectionBound.result _ env heap n getN) .nil) rfl loop⟩

private def stages (directions : List Direction) : List Stmt :=
  directions.map (fun direction => .augAssign (.name "products") .add (collection direction))

private theorem stages.result (directions : List Direction) (heap : Mutable.Heap) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (items : List Int) (garbage : Mutable.Heap) (n : Int) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getN : env "n" = some (.scalar (.int n)))
    (getProducts : env "products" = some (.ref heap.length)) :
    ∃ finalEnv finalItems finalGarbage, HeapCalls.BlockContinues program env (stages directions)
      (heap ++ .list (integers items) :: garbage) finalEnv
      (heap ++ .list (integers finalItems) :: finalGarbage) ∧
      finalEnv "products" = some (.ref heap.length) := by
  induction directions generalizing items garbage env with
  | nil => exact ⟨env, items, garbage, HeapCalls.BlockContinues.nil, getProducts⟩
  | cons direction directions ih =>
      let current := heap ++ .list (integers items) :: garbage
      obtain ⟨more, evaluated⟩ := collection.result direction current address (typed.append _) n env getGrid getN
      let nextEnv := HeapCalls.setLocal env "products" (.ref heap.length)
      let nextItems := items ++ more
      let nextGarbage := garbage ++ [.list (integers more)]
      have append : HeapCalls.BlockContinues program env
          [.augAssign (.name "products") .add (collection direction)] current nextEnv
          (heap ++ .list (integers nextItems) :: nextGarbage) := by
        apply HeapCalls.BlockContinues.augAssign getProducts evaluated
        have left : (current ++ [.list (integers more)])[heap.length]? = some (.list (integers items)) := by
          simp [current, List.append_assoc]
        have right : (current ++ [.list (integers more)])[current.length]? = some (.list (integers more)) := by simp
        rw [HeapCalls.inplace_add_lists _ _ _ _ _ left right]
        simp [current, nextItems, nextGarbage, integers, List.append_assoc, List.map_append]
      obtain ⟨finalEnv, finalItems, finalGarbage, rest, products⟩ := ih nextItems nextGarbage nextEnv
        (by simpa [nextEnv, HeapCalls.setLocal] using getGrid)
        (by simpa [nextEnv, HeapCalls.setLocal] using getN) rfl
      exact ⟨finalEnv, finalItems, finalGarbage, append.append rest, products⟩

private abbrev maximumExpression : Expr :=
  .ifExp (.name "products") (.builtinCall .max [.name "products"]) (.constant (.int 0))

private theorem maximum.result (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (integers items))) (env : HeapCalls.Env)
    (getProducts : env "products" = some (.ref address)) :
    ∃ answer : Int, HeapCalls.Evaluates program env maximumExpression heap (.scalar (.int answer)) heap := by
  cases items with
  | nil =>
      refine ⟨0, HeapCalls.Evaluates.conditional (flag := false) (HeapCalls.Evaluates.lookup getProducts) ?_
        HeapCalls.Evaluates.constant⟩
      simp [Mutable.truth, found, integers]
  | cons first rest =>
      refine ⟨rest.foldl max first, HeapCalls.Evaluates.conditional (flag := true)
        (HeapCalls.Evaluates.lookup getProducts) ?_ ?_⟩
      · simp [Mutable.truth, found, integers]
      · apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup getProducts) .nil)
        simp [HeapCalls.primitive, Mutable.sequence, found, integers, List.mapM_map,
          Function.comp_def, ScalarSet.maximum, ScalarSet.maximumFrom_ints, List.mapM_pure, HeapCalls.scalarResult]

theorem naive.result (heap : Mutable.Heap) (address : Nat) (n : Int)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    ∃ answer finalHeap, HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int n)] heap
      (.scalar (.int answer)) finalHeap := by
  let initialEnv := HeapCalls.setLocal (HeapCalls.argumentEnv
    [⟨"grid", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩,
      ⟨"n", some (.name "int"), none⟩] [.ref address, .scalar (.int n)]) "products" (.ref heap.length)
  obtain ⟨finalEnv, items, garbage, collected, products⟩ := stages.result
    [.right, .down, .downRight, .downLeft] heap address typed [] [] n initialEnv rfl rfl rfl
  obtain ⟨answer, maximum⟩ := maximum.result (heap ++ .list (integers items) :: garbage)
    heap.length items (by simp) finalEnv products
  refine ⟨answer, heap ++ .list (integers items) :: garbage, HeapCalls.BlockReturns.function rfl rfl ?_⟩
  apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.list .nil)
  exact collected.returns (HeapCalls.BlockReturns.return_value maximum)

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (n : Int) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "naive" [.ref address, .scalar (.int n)] heap).Returns := by
  obtain ⟨answer, finalHeap, executed⟩ := naive.result heap address n typed
  exact executed.returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (n : Int) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "naive" [.ref address, .scalar (.int n)] heap).Supported :=
  (naive.«Returns» heap address n valid typed).supported

/-- A mathematical grid represented by shared Python lists. Row addresses may repeat. -/
structure GridView (heap : Mutable.Heap) (address : Nat) (grid : List (List Nat)) where
  rows : List Nat
  found : heap[address]? = some (.list (rows.map Mutable.Value.ref))
  size : rows.length = grid.length
  contents : ∀ i (within : i < rows.length),
    heap[rows[i]]? = some (.list ((grid[i]'(by omega)).map (fun (n : Nat) => .scalar (.int (n : Int)))))

/-- Unrelated allocation or updates outside the grid do not change its interpretation. -/
def GridView.preserve {heap other : Mutable.Heap} {address : Nat} {grid : List (List Nat)}
    (view : GridView heap address grid)
    (preserved : ∀ (index : Nat) (object : Mutable.Object),
      heap[index]? = some object → other[index]? = some object) : GridView other address grid :=
  ⟨view.rows, preserved _ _ view.found, view.size,
    fun i within => preserved _ _ (view.contents i within)⟩

def GridView.append {heap : Mutable.Heap} {address : Nat} {grid : List (List Nat)}
    (view : GridView heap address grid) (extra : Mutable.Heap) : GridView (heap ++ extra) address grid := by
  apply view.preserve
  intro index object found
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_append_left within]
  exact found

private theorem grid_val.block_exact (heap : Mutable.Heap) (address : Nat) (grid : List (List Nat))
    (view : GridView heap address grid) (env : HeapCalls.Env) (r c : Int)
    (getGrid : env "grid" = some (.ref address))
    (getRow : env "r" = some (.scalar (.int r)))
    (getColumn : env "c" = some (.scalar (.int c))) :
    HeapCalls.BlockReturns program env gridBody heap
      (.scalar (.int (↑(ProjectEulerStatements.Grid.get grid r c 0)))) heap := by
  have rowGuard := bounded.result env heap (.name "r") (.builtinCall .len [.name "grid"]) r grid.length
    (HeapCalls.Evaluates.lookup getRow)
    (HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup getGrid) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, view.found, view.size]))
  by_cases rowValid : 0 ≤ r ∧ r < grid.length
  · have rowIndex : r.toNat < grid.length := by omega
    have addressIndex : r.toNat < view.rows.length := by rw [view.size]; exact rowIndex
    let row := view.rows[r.toNat]
    let values := grid[r.toNat]
    have contents := view.contents r.toNat addressIndex
    have readRow : HeapCalls.Evaluates program env rowExpression heap (.ref row) heap := by
      apply HeapCalls.Evaluates.subscript (by intros a b c impossible; cases impossible)
        (HeapCalls.Evaluates.lookup getGrid) (HeapCalls.Evaluates.lookup getRow)
      have read := Mutable.getItem_list heap address r.toNat (view.rows.map Mutable.Value.ref)
        view.found (by simpa using addressIndex)
      rw [List.getElem_map] at read
      simpa [Int.toNat_of_nonneg rowValid.1, row] using read
    have columnGuard := bounded.result env heap (.name "c") (.builtinCall .len [rowExpression]) c values.length
      (HeapCalls.Evaluates.lookup getColumn)
      (HeapCalls.Evaluates.builtin (.cons readRow .nil) (by simp [HeapCalls.primitive, Mutable.length, contents, row, values]))
    have wholeGuard : HeapCalls.Evaluates program env condition heap
        (.scalar (.bool (decide (0 ≤ c ∧ c < values.length)))) heap := by
      apply HeapCalls.Evaluates.boolean_next (flag := true)
        (value := .scalar (.bool true)) (middle := heap)
      · simpa [rowValid] using rowGuard
      · rfl
      · rfl
      · exact HeapCalls.Evaluates.boolean_last columnGuard rfl
    by_cases columnValid : 0 ≤ c ∧ c < values.length
    · have columnIndex : c.toNat < values.length := by omega
      have result : ProjectEulerStatements.Grid.get grid r c 0 = values[c.toNat] := by
        simp [ProjectEulerStatements.Grid.get, rowValid.1, columnValid.1,
          List.getElem?_eq_getElem rowIndex, values, List.getElem?_eq_getElem columnIndex]
      rw [result]
      apply HeapCalls.BlockReturns.return_value
      apply HeapCalls.Evaluates.conditional (flag := true)
        (value := .scalar (.bool true)) (middle := heap)
      · simpa [columnValid] using wholeGuard
      · rfl
      · apply HeapCalls.Evaluates.subscript (by intros a b c impossible; cases impossible)
          readRow (HeapCalls.Evaluates.lookup getColumn)
        have read := Mutable.getItem_list heap row c.toNat (values.map (fun (n : Nat) => .scalar (.int (n : Int)))) contents
          (by simpa using columnIndex)
        rw [List.getElem_map] at read
        simpa [Int.toNat_of_nonneg columnValid.1] using read
    · have result : ProjectEulerStatements.Grid.get grid r c 0 = 0 := by
        by_cases nonnegative : 0 ≤ c
        · have outside : values.length ≤ c.toNat := by omega
          simp [ProjectEulerStatements.Grid.get, rowValid.1, nonnegative,
            List.getElem?_eq_getElem rowIndex, List.getElem?_eq_none outside, values]
        · simp [ProjectEulerStatements.Grid.get, nonnegative]
      rw [result]
      apply HeapCalls.BlockReturns.return_value
      exact HeapCalls.Evaluates.conditional (flag := false)
        (by simpa [columnValid] using wholeGuard) rfl HeapCalls.Evaluates.constant
  · have result : ProjectEulerStatements.Grid.get grid r c 0 = 0 := by
      by_cases nonnegative : 0 ≤ r
      · have outside : grid.length ≤ r.toNat := by omega
        simp [ProjectEulerStatements.Grid.get, nonnegative, List.getElem?_eq_none outside]
      · simp [ProjectEulerStatements.Grid.get, nonnegative]
    rw [result]
    apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.conditional (flag := false) (value := .scalar (.bool false)) (middle := heap)
    · exact HeapCalls.Evaluates.boolean_stop (flag := false) (by simpa [rowValid] using rowGuard) rfl rfl
    · rfl
    · exact HeapCalls.Evaluates.constant

/-- The source accessor returns precisely the mathematical padded grid value. -/
theorem grid_val.exact (heap : Mutable.Heap) (address : Nat) (grid : List (List Nat))
    (view : GridView heap address grid) (r c : Int) :
    HeapCalls.ReturnsValue program "grid_val" [.ref address, .scalar (.int r), .scalar (.int c)] heap
      (.scalar (.int (↑(ProjectEulerStatements.Grid.get grid r c 0)))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact grid_val.block_exact heap address grid view _ r c rfl rfl rfl

private theorem product.loop_exact (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (grid : List (List Nat)) (view : GridView heap address grid) (r c n position : Nat)
    (env : HeapCalls.Env) (acc : Int)
    (getGrid : env "grid" = some (.ref address))
    (getRow : env "r" = some (.scalar (.int r)))
    (getColumn : env "c" = some (.scalar (.int c)))
    (getAcc : env "acc" = some (.scalar (.int acc))) :
    ∃ finalEnv, HeapCalls.BlockContinues program env
      [.rangeStepLoop "i" position n 1 (productBody direction) []] heap finalEnv heap ∧
      finalEnv "acc" = some (.scalar (.int
        (acc * ProjectEulerStatements.Grid.segmentTail grid direction r c position n))) := by
  by_cases active : position < n
  · let indexed := HeapCalls.setLocal env "i" (.scalar (.int position))
    have savedGrid : indexed "grid" = some (.ref address) := by simpa [indexed, HeapCalls.setLocal] using getGrid
    have savedRow : indexed "r" = some (.scalar (.int r)) := by simpa [indexed, HeapCalls.setLocal] using getRow
    have savedColumn : indexed "c" = some (.scalar (.int c)) := by simpa [indexed, HeapCalls.setLocal] using getColumn
    have savedAcc : indexed "acc" = some (.scalar (.int acc)) := by simpa [indexed, HeapCalls.setLocal] using getAcc
    obtain ⟨row, column⟩ := offsets.result direction indexed heap r c position savedRow savedColumn rfl
    let value := ProjectEulerStatements.Grid.get grid (direction.row r position) (direction.column c position) 0
    have evaluated := grid_val.exact heap address grid view (direction.row r position) (direction.column c position)
    let nextEnv := HeapCalls.setLocal indexed "acc" (.scalar (.int (acc * value)))
    have step : HeapCalls.BlockContinues program indexed (productBody direction) heap nextEnv heap := by
      apply HeapCalls.BlockContinues.augAssign savedAcc
        (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup savedGrid) (.cons row (.cons column .nil))) evaluated)
      rfl
    obtain ⟨finalEnv, rest, result⟩ := product.loop_exact direction heap address grid view r c n
      (position + 1) nextEnv (acc * value)
      (by simpa [nextEnv, HeapCalls.setLocal] using savedGrid)
      (by simpa [nextEnv, HeapCalls.setLocal] using savedRow)
      (by simpa [nextEnv, HeapCalls.setLocal] using savedColumn) rfl
    refine ⟨finalEnv, ?_, ?_⟩
    · apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
      simpa only [Nat.cast_add, Nat.cast_one] using step.append rest
    · rw [ProjectEulerStatements.Grid.segmentTail_step grid direction r c position n active]
      simpa only [Nat.cast_mul, Int.mul_assoc] using result
  · refine ⟨env, HeapCalls.BlockContinues.range_done
      (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil, ?_⟩
    simpa [ProjectEulerStatements.Grid.segmentTail_done grid direction r c position n (by omega)] using getAcc
termination_by n - position
decreasing_by omega

/-- All four source loops compute their corresponding mathematical segment products. -/
theorem product.exact (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (grid : List (List Nat)) (view : GridView heap address grid) (r c n : Nat) :
    HeapCalls.ReturnsValue program (productName direction)
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)] heap
      (.scalar (.int (↑(ProjectEulerStatements.Grid.segmentProduct grid direction r c n)))) heap := by
  let initialEnv := HeapCalls.setLocal (HeapCalls.argumentEnv productArgs
    [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int n)]) "acc" (.scalar (.int 1))
  obtain ⟨finalEnv, loop, result⟩ := product.loop_exact direction heap address grid view r c n 0
    initialEnv 1 rfl rfl rfl rfl
  apply HeapCalls.BlockReturns.function (args := productArgs)
    (body := [.expr (.constant (.string "\n    @formalsw: Returns\n    ")),
      .assign [.name "acc"] (.constant (.int 1)),
      .forIn (.name "i") (.call (.name "range") [.name "n"]) (productBody direction) [],
      .return (.name "acc")])
    (by cases direction <;> rfl) rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockContinues.returns
    (HeapCalls.BlockContinues.for_range (.cons (HeapCalls.Evaluates.lookup (name := "n") rfl) .nil) rfl loop)
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup
    (by simpa [ProjectEulerStatements.Grid.segmentTail_zero] using result))

private theorem product.empty (direction : Direction) (heap : Mutable.Heap) (address : Nat) (r c : Int) :
    HeapCalls.ReturnsValue program (productName direction)
      [.ref address, .scalar (.int r), .scalar (.int c), .scalar (.int 0)] heap
      (.scalar (.int 1)) heap := by
  apply HeapCalls.BlockReturns.function (args := productArgs)
    (body := [.expr (.constant (.string "\n    @formalsw: Returns\n    ")),
      .assign [.name "acc"] (.constant (.int 1)),
      .forIn (.name "i") (.call (.name "range") [.name "n"]) (productBody direction) [],
      .return (.name "acc")])
    (by cases direction <;> rfl) rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockContinues.returns
    (HeapCalls.BlockContinues.for_range (.cons (HeapCalls.Evaluates.lookup (name := "n") rfl) .nil) rfl
      (HeapCalls.BlockContinues.range_done rfl HeapCalls.BlockContinues.nil))
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

private theorem collectionElement.exact (direction : Direction) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (address : Nat) (grid : List (List Nat)) (view : GridView heap address grid) (r c n : Nat)
    (getGrid : env "grid" = some (.ref address)) (getR : env "r" = some (.scalar (.int r)))
    (getC : env "c" = some (.scalar (.int c))) (getN : env "n" = some (.scalar (.int n))) :
    HeapCalls.Evaluates program env (collectionElement direction) heap
      (.scalar (.int (↑(ProjectEulerStatements.Grid.segmentProduct grid direction r
        (ProjectEulerStatements.Grid.columnStart direction c n) n)))) heap := by
  let column : Int := if direction = .downLeft then c + n - 1 else c
  have readColumn : HeapCalls.Evaluates program env (collectionColumn direction) heap (.scalar (.int column)) heap := by
    cases direction
    all_goals first
      | exact HeapCalls.Evaluates.lookup getC
      | exact HeapCalls.Evaluates.binary
          (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getC) (HeapCalls.Evaluates.lookup getN) rfl)
          HeapCalls.Evaluates.constant rfl
  apply HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup getGrid)
    (.cons (HeapCalls.Evaluates.lookup getR) (.cons readColumn (.cons (HeapCalls.Evaluates.lookup getN) .nil))))
  by_cases zero : n = 0
  · subst n
    exact product.empty direction heap address r column
  · have columnEq : column = (ProjectEulerStatements.Grid.columnStart direction c n : Int) := by
      cases direction <;> simp [column, ProjectEulerStatements.Grid.columnStart]
      omega
    rw [columnEq]
    exact product.exact direction heap address grid view r _ n

private abbrev naturals (items : List Nat) : List Mutable.Value :=
  items.map (fun (value : Nat) => .scalar (.int (value : Int)))

private theorem collection.inner_exact (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (grid : List (List Nat)) (view : GridView heap address grid)
    (items : List Nat) (position r n : Nat) (stop : Int) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getR : env "r" = some (.scalar (.int r)))
    (getN : env "n" = some (.scalar (.int n))) :
    ∃ finalEnv, HeapCalls.BlockContinues program env
      [.rangeStepLoop "c" position stop 1 (collectionInner direction heap.length) []]
      (heap ++ [.list (naturals items)]) finalEnv
      (heap ++ [.list (naturals (items ++ ProjectEulerStatements.Grid.rowProducts grid direction r n position stop.toNat))]) ∧
      finalEnv "grid" = some (.ref address) ∧ finalEnv "n" = some (.scalar (.int n)) := by
  by_cases active : (position : Int) < stop
  · let boundEnv := HeapCalls.setLocal env "c" (.scalar (.int position))
    have savedGrid : boundEnv "grid" = some (.ref address) := by simpa [boundEnv, HeapCalls.setLocal] using getGrid
    have row : boundEnv "r" = some (.scalar (.int r)) := by simpa [boundEnv, HeapCalls.setLocal] using getR
    have count : boundEnv "n" = some (.scalar (.int n)) := by simpa [boundEnv, HeapCalls.setLocal] using getN
    let answer := ProjectEulerStatements.Grid.segmentProduct grid direction r
      (ProjectEulerStatements.Grid.columnStart direction position n) n
    have element := collectionElement.exact direction boundEnv _ address grid (view.append [.list (naturals items)]) r position n
      savedGrid row rfl count
    have emitted : HeapCalls.BlockContinues program boundEnv (collectionInner direction heap.length)
        (heap ++ [.list (naturals items)]) boundEnv (heap ++ [.list (naturals (items ++ [answer]))]) := by
      have write := HeapCalls.BlockContinues.comprehension_append (address := heap.length) element
        (by simp : (heap ++ [.list (naturals items)])[heap.length]? = some (.list (naturals items)))
      simpa [collectionInner, naturals, List.map_append, answer] using write
    obtain ⟨finalEnv, rest, savedGrid, count⟩ := collection.inner_exact direction heap address grid view
      (items ++ [answer]) (position + 1) r n stop boundEnv savedGrid row count
    refine ⟨finalEnv, ?_, savedGrid, count⟩
    rw [ProjectEulerStatements.Grid.rowProducts_step grid direction r n position stop.toNat (by omega)]
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
    simpa [collectionInner, Calls.loopContinuation, Calls.loopControl, Nat.cast_add, Nat.cast_one,
      List.append_assoc, answer] using emitted.append rest
  · refine ⟨env, ?_, getGrid, getN⟩
    rw [ProjectEulerStatements.Grid.rowProducts_done grid direction r n position stop.toNat (by omega)]
    simp only [List.append_nil]
    exact HeapCalls.BlockContinues.range_done
      (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil
termination_by stop.toNat - position
decreasing_by omega

private theorem collection.outer_exact (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (grid : List (List Nat)) (view : GridView heap address grid)
    (items : List Nat) (position n : Nat) (stop : Int) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getN : env "n" = some (.scalar (.int n))) :
    ∃ finalEnv, HeapCalls.BlockContinues program env
      [.rangeStepLoop "r" position stop 1 (collectionOuter direction heap.length) []]
      (heap ++ [.list (naturals items)]) finalEnv
      (heap ++ [.list (naturals (items ++ ProjectEulerStatements.Grid.gridProductsTail grid direction n position
        stop.toNat (collectionStop (direction == .down) n).toNat))]) ∧
      finalEnv "grid" = some (.ref address) ∧ finalEnv "n" = some (.scalar (.int n)) := by
  by_cases active : (position : Int) < stop
  · let boundEnv := HeapCalls.setLocal env "r" (.scalar (.int position))
    have savedGrid : boundEnv "grid" = some (.ref address) := by simpa [boundEnv, HeapCalls.setLocal] using getGrid
    have count : boundEnv "n" = some (.scalar (.int n)) := by simpa [boundEnv, HeapCalls.setLocal] using getN
    let more := ProjectEulerStatements.Grid.rowProducts grid direction position n 0
      (collectionStop (direction == .down) n).toNat
    obtain ⟨middleEnv, inner, middleGrid, middleCount⟩ := collection.inner_exact direction heap address grid view
      items 0 position n (collectionStop (direction == .down) n) boundEnv savedGrid rfl count
    have entered : HeapCalls.BlockContinues program boundEnv (collectionOuter direction heap.length)
        (heap ++ [.list (naturals items)]) middleEnv (heap ++ [.list (naturals (items ++ more))]) :=
      HeapCalls.BlockContinues.for_range (.cons (collectionBound.result _ boundEnv _ n count) .nil) rfl inner
    obtain ⟨finalEnv, rest, finalGrid, finalCount⟩ := collection.outer_exact direction heap address grid view
      (items ++ more) (position + 1) n stop middleEnv middleGrid middleCount
    refine ⟨finalEnv, ?_, finalGrid, finalCount⟩
    rw [ProjectEulerStatements.Grid.gridProductsTail_step grid direction n position stop.toNat _ (by omega)]
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues, active])
    simpa [collectionOuter, Calls.loopContinuation, Calls.loopControl, Nat.cast_add, Nat.cast_one,
      List.append_assoc, more] using entered.append rest
  · refine ⟨env, ?_, getGrid, getN⟩
    rw [ProjectEulerStatements.Grid.gridProductsTail_done grid direction n position stop.toNat _ (by omega)]
    simp only [List.append_nil]
    exact HeapCalls.BlockContinues.range_done
      (by simp [Calls.rangeContinues, active]) HeapCalls.BlockContinues.nil
termination_by stop.toNat - position
decreasing_by omega

private abbrev directionProducts (grid : List (List Nat)) (direction : Direction) (n : Nat) :=
  (ProjectEulerStatements.Grid.starts direction 20 20 n).map fun (r, c) =>
    ProjectEulerStatements.Grid.segmentProduct grid direction r c n

private theorem collection.exact (direction : Direction) (heap : Mutable.Heap) (address : Nat)
    (grid : List (List Nat)) (view : GridView heap address grid) (n : Nat) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getN : env "n" = some (.scalar (.int n))) :
    HeapCalls.Evaluates program env (collection direction) heap (.ref heap.length)
      (heap ++ [.list (naturals (directionProducts grid direction n))]) := by
  let localEnv := HeapCalls.comprehensionEnv env
    [("r", .call (.name "range") [collectionBound (direction == .right)], []),
     ("c", .call (.name "range") [collectionBound (direction == .down)], [])]
  have savedGrid : localEnv "grid" = some (.ref address) := by simpa [localEnv, HeapCalls.comprehensionEnv] using getGrid
  have count : localEnv "n" = some (.scalar (.int n)) := by simpa [localEnv, HeapCalls.comprehensionEnv] using getN
  obtain ⟨finalEnv, loop, _, _⟩ := collection.outer_exact direction heap address grid view [] 0 n
    (collectionStop (direction == .right) n) localEnv savedGrid count
  have stops (full : Bool) : (collectionStop full n).toNat = if full then 20 else 21 - n := by
    cases full
    · simp only [collectionStop, Bool.false_eq_true, ↓reduceIte]
      omega
    · rfl
  have candidates : ProjectEulerStatements.Grid.gridProductsTail grid direction n 0
      (collectionStop (direction == .right) n).toNat (collectionStop (direction == .down) n).toNat =
      directionProducts grid direction n := by
    rw [stops, stops]
    simpa only [beq_iff_eq] using ProjectEulerStatements.Grid.gridProductsTail_zero grid direction 20 20 n
  rw [candidates] at loop
  exact HeapCalls.Evaluates.list_comp_range
    (.cons (collectionBound.result _ env heap n getN) .nil) rfl loop

private theorem stages.exact (directions : List Direction) (heap : Mutable.Heap) (address : Nat)
    (grid : List (List Nat)) (view : GridView heap address grid)
    (items : List Nat) (garbage : Mutable.Heap) (n : Nat) (env : HeapCalls.Env)
    (getGrid : env "grid" = some (.ref address)) (getN : env "n" = some (.scalar (.int n)))
    (getProducts : env "products" = some (.ref heap.length)) :
    ∃ finalEnv finalGarbage, HeapCalls.BlockContinues program env (stages directions)
      (heap ++ .list (naturals items) :: garbage) finalEnv
      (heap ++ .list (naturals (items ++ directions.flatMap (fun direction => directionProducts grid direction n))) :: finalGarbage) ∧
      finalEnv "products" = some (.ref heap.length) := by
  induction directions generalizing items garbage env with
  | nil => exact ⟨env, garbage, by simpa [stages] using (HeapCalls.BlockContinues.nil (module := program) (env := env) (heap := heap ++ .list (naturals items) :: garbage)), getProducts⟩
  | cons direction directions ih =>
      let current := heap ++ .list (naturals items) :: garbage
      let more := directionProducts grid direction n
      have evaluated := collection.exact direction current address grid (view.append _) n env getGrid getN
      let nextEnv := HeapCalls.setLocal env "products" (.ref heap.length)
      let nextItems := items ++ more
      let nextGarbage := garbage ++ [.list (naturals more)]
      have appended : HeapCalls.BlockContinues program env
          [.augAssign (.name "products") .add (collection direction)] current nextEnv
          (heap ++ .list (naturals nextItems) :: nextGarbage) := by
        apply HeapCalls.BlockContinues.augAssign getProducts evaluated
        have left : (current ++ [.list (naturals more)])[heap.length]? = some (.list (naturals items)) := by
          simp [current, List.append_assoc]
        have right : (current ++ [.list (naturals more)])[current.length]? = some (.list (naturals more)) := by simp
        rw [HeapCalls.inplace_add_lists _ _ _ _ _ left right]
        simp [current, nextItems, nextGarbage, naturals, List.append_assoc, List.map_append]
      obtain ⟨finalEnv, finalGarbage, rest, products⟩ := ih nextItems nextGarbage nextEnv
        (by simpa [nextEnv, HeapCalls.setLocal] using getGrid)
        (by simpa [nextEnv, HeapCalls.setLocal] using getN) rfl
      refine ⟨finalEnv, finalGarbage, ?_, products⟩
      simpa [stages, List.append_assoc, nextItems, more] using appended.append rest

private theorem maximum.exact (heap : Mutable.Heap) (address : Nat) (items : List Nat)
    (found : heap[address]? = some (.list (naturals items))) (env : HeapCalls.Env)
    (getProducts : env "products" = some (.ref address)) :
    HeapCalls.Evaluates program env maximumExpression heap
      (.scalar (.int (↑(items.foldl max 0)))) heap := by
  cases items with
  | nil =>
      apply HeapCalls.Evaluates.conditional (flag := false) (HeapCalls.Evaluates.lookup getProducts) _
        HeapCalls.Evaluates.constant
      simp [Mutable.truth, found, naturals]
  | cons first rest =>
      have folded : (rest.map (fun (n : Nat) => (n : Int))).foldl max (first : Int) =
          ((rest.foldl max first : Nat) : Int) :=
        ProjectEulerStatements.ListMaximum.fold_map (fun (n : Nat) => (n : Int))
          (by intro a b; dsimp; omega) rest first
      have maximum : Calls.maximumFrom (.int first) (rest.map (fun (n : Nat) => Constant.int n)) =
          .ok (.int (↑(rest.foldl max first))) := by
        simpa only [List.map_map, Function.comp_def, folded] using
          ScalarSet.maximumFrom_ints (rest.map (fun (n : Nat) => (n : Int))) first
      apply HeapCalls.Evaluates.conditional (flag := true)
        (HeapCalls.Evaluates.lookup getProducts)
      · simp [Mutable.truth, found, naturals]
      · apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup getProducts) .nil)
        simp [HeapCalls.primitive, Mutable.sequence, found, naturals, List.mapM_map,
          Function.comp_def, ScalarSet.maximum, HeapCalls.scalarResult, List.mapM_pure, maximum]

/-- The naïve Python function computes the exact directional maximum and leaves
all pre-existing heap objects unchanged. Fresh candidate lists are private. -/
theorem naive.exact (heap : Mutable.Heap) (address : Nat) (grid : List (List Nat))
    (view : GridView heap address grid) (n : Nat) :
    ∃ extra, HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int n)] heap
      (.scalar (.int (↑((ProjectEulerStatements.Grid.directionalProducts grid 20 20 n).foldl max 0))))
      (heap ++ extra) := by
  let initialEnv := HeapCalls.setLocal (HeapCalls.argumentEnv
    [⟨"grid", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩,
      ⟨"n", some (.name "int"), none⟩] [.ref address, .scalar (.int n)]) "products" (.ref heap.length)
  obtain ⟨finalEnv, garbage, collected, products⟩ := stages.exact
    [.right, .down, .downRight, .downLeft] heap address grid view [] [] n initialEnv rfl rfl rfl
  let items := ProjectEulerStatements.Grid.directionalProducts grid 20 20 n
  have maximum := maximum.exact (heap ++ .list (naturals items) :: garbage)
    heap.length items (by simp) finalEnv products
  refine ⟨.list (naturals items) :: garbage, HeapCalls.BlockReturns.function rfl rfl ?_⟩
  apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.list .nil)
  exact collected.returns (HeapCalls.BlockReturns.return_value maximum)

end data.«project-euler-statements».data.py.project_euler_statements.p11
