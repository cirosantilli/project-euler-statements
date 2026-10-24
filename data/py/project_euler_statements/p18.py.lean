import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p18.py.ast»
import FormalSW
import ProjectEulerStatements.Lib.TrianglePaths

namespace data.«project-euler-statements».data.py.project_euler_statements.p18
open FormalSW.PyAst
open ProjectEulerStatements.P18 (rowTotals)
private abbrev program := P18Ast.module
private abbrev encode (values : List Int) : List Mutable.Value :=
  values.map (fun n => .scalar (.int n))

/-- The result list and zip tuples are private; input objects remain in the prefix. -/
private def workHeap (base : Mutable.Heap) (output : List Int) (scratch : Mutable.Heap) : Mutable.Heap :=
  base ++ [.list (encode output)] ++ scratch

private theorem workHeap.read (base scratch : Mutable.Heap) (output : List Int)
    (address : Nat) (object : Mutable.Object) (found : base[address]? = some object) :
    (workHeap base output scratch)[address]? = some object := by
  have bounded : address < base.length := (List.getElem?_eq_some_iff.mp found).choose
  simpa [workHeap, List.append_assoc, List.getElem?_append_left bounded] using found

private theorem workHeap.output (base scratch : Mutable.Heap) (output : List Int) :
    (workHeap base output scratch)[base.length]? = some (.list (encode output)) := by
  simp [workHeap, List.append_assoc]

private theorem workHeap.append (base scratch : Mutable.Heap) (output : List Int) (value : Int) :
    (workHeap base output scratch).set base.length (.list (encode (output ++ [value]))) =
      workHeap base (output ++ [value]) scratch := by
  simp [workHeap, List.append_assoc]

private theorem zip.read (heap : Mutable.Heap) (rowAddress belowAddress tailAddress : Nat)
    (row below : List Int) (position : Nat)
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (getBelow : heap[belowAddress]? = some (.list (encode below)))
    (getTail : heap[tailAddress]? = some (.list (encode below.tail))) :
    HeapCalls.zipItem [.ref rowAddress, .ref belowAddress, .ref tailAddress] position heap =
      some (.ok (do
        let x ← row[position]?
        let y ← below[position]?
        let z ← below[position + 1]?
        pure [.scalar (.int x), .scalar (.int y), .scalar (.int z)]), heap) := by
  cases hx : row[position]? <;> cases hy : below[position]? <;> cases hz : below[position + 1]? <;>
    simp [HeapCalls.zipItem, HeapCalls.zipFields, HeapCalls.sequenceValue, Mutable.sequence,
      getRow, getBelow, getTail, encode, hx, hy, hz, Except.map]

private abbrev rowElement : Expr :=
  .binOp (.name "x") .add (.builtinCall .max [.name "y", .name "z"])

private theorem rowElement.result (env : HeapCalls.Env) (heap : Mutable.Heap) (x y z : Int)
    (getX : env "x" = some (.scalar (.int x)))
    (getY : env "y" = some (.scalar (.int y)))
    (getZ : env "z" = some (.scalar (.int z))) :
    HeapCalls.Evaluates program env rowElement heap (.scalar (.int (x + max y z))) heap := by
  apply HeapCalls.Evaluates.binary (bv := .scalar (.int (max y z))) (afterRight := heap)
    (.lookup getX) ?_ rfl
  apply HeapCalls.Evaluates.builtin (.cons (.lookup getY) (.cons (.lookup getZ) .nil))
  by_cases larger : y < z
  · simp [HeapCalls.primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare,
      evalCmpOp, HeapCalls.scalarResult, List.mapM, List.mapM.loop, larger, max_eq_right (le_of_lt larger)]
  · simp [HeapCalls.primitive, Calls.positionalMaximum, Calls.maximumFrom, scalarCompare,
      evalCmpOp, HeapCalls.scalarResult, List.mapM, List.mapM.loop, larger, max_eq_left (le_of_not_gt larger)]

private abbrev rowBody (address : Nat) : List Stmt :=
  [.assign [.tuple [.name "x", .name "y", .name "z"]] (.name "$formalsw.unpack"),
    .comprehensionAppend address rowElement]

private theorem rowLoop.result (base scratch : Mutable.Heap) (row below output : List Int)
    (rowAddress belowAddress tailAddress position : Nat) (env : HeapCalls.Env)
    (getRow : base[rowAddress]? = some (.list (encode row)))
    (getBelow : base[belowAddress]? = some (.list (encode below)))
    (getTail : base[tailAddress]? = some (.list (encode below.tail))) :
    ∃ finalEnv finalScratch, HeapCalls.BlockContinues program env
      [.zipStepLoop "$formalsw.unpack" [.ref rowAddress, .ref belowAddress, .ref tailAddress]
        position (rowBody base.length) []]
      (workHeap base output scratch) finalEnv
      (workHeap base (output ++ (rowTotals row below).drop position) finalScratch) := by
  let heap := workHeap base output scratch
  have readZip := zip.read heap rowAddress belowAddress tailAddress row below position
    (workHeap.read base scratch output _ _ getRow)
    (workHeap.read base scratch output _ _ getBelow)
    (workHeap.read base scratch output _ _ getTail)
  by_cases active : position < min row.length (below.length - 1)
  · have inRow : position < row.length := lt_of_lt_of_le active (Nat.min_le_left _ _)
    have inNext : position + 1 < below.length := by
      have := lt_of_lt_of_le active (Nat.min_le_right _ _)
      omega
    have inBelow : position < below.length := by omega
    let x := row[position]
    let y := below[position]
    let z := below[position + 1]
    let fields := encode [x, y, z]
    let moreScratch := scratch ++ [.tuple fields]
    let afterTuple := workHeap base output moreScratch
    let tupleEnv := HeapCalls.setLocal env "$formalsw.unpack" (.ref heap.length)
    let assigned := HeapCalls.assignNames tupleEnv ["x", "y", "z"] fields
    have fetched : HeapCalls.zipItem [.ref rowAddress, .ref belowAddress, .ref tailAddress]
        position heap = some (.ok (some fields), heap) := by
      simpa [List.getElem?_eq_getElem inRow, List.getElem?_eq_getElem inBelow,
        List.getElem?_eq_getElem inNext, x, y, z, fields, encode] using readZip
    have allocated : Mutable.allocateTuple fields heap = some (.ok (.ref heap.length), afterTuple) := by
      simp [Mutable.allocateTuple, fields, encode, afterTuple, moreScratch, heap, workHeap,
        List.append_assoc, Except.map]
    have tupleFound : Mutable.sequence (.ref heap.length) afterTuple = some (.ok fields, afterTuple) := by
      have same : afterTuple = heap ++ [.tuple fields] := by
        simp [afterTuple, moreScratch, heap, workHeap, List.append_assoc]
      simp [same, Mutable.sequence]
    have unpacked : HeapCalls.BlockContinues program tupleEnv
        [.assign [.tuple [.name "x", .name "y", .name "z"]] (.name "$formalsw.unpack")]
        afterTuple assigned afterTuple :=
      HeapCalls.BlockContinues.unpack rfl (.lookup rfl) tupleFound rfl
    have emitted : HeapCalls.BlockContinues program assigned
        [.comprehensionAppend base.length rowElement] afterTuple assigned
        (workHeap base (output ++ [x + max y z]) moreScratch) := by
      have step := HeapCalls.BlockContinues.comprehension_append (globals := [])
        (rowElement.result assigned afterTuple x y z rfl rfl rfl)
        (workHeap.output base moreScratch output)
      simpa [afterTuple, workHeap, encode, List.map_append, List.append_assoc] using step
    obtain ⟨finalEnv, finalScratch, continued⟩ := rowLoop.result base moreScratch row below
      (output ++ [x + max y z]) rowAddress belowAddress tailAddress (position + 1) assigned getRow getBelow getTail
    have inTotals : position < (rowTotals row below).length := by
      simpa [ProjectEulerStatements.P18.rowTotals_length] using active
    have total : (rowTotals row below)[position] = x + max y z := by
      have indexed := ProjectEulerStatements.P18.rowTotals_getElem? row below position
      simpa [List.getElem?_eq_getElem inTotals, List.getElem?_eq_getElem inRow,
        List.getElem?_eq_getElem inBelow, List.getElem?_eq_getElem inNext, x, y, z] using indexed
    refine ⟨finalEnv, finalScratch, HeapCalls.BlockContinues.zip_step fetched allocated ?_⟩
    have rest := (unpacked.append emitted).append continued
    simpa [rowBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
      List.drop_eq_getElem_cons inTotals, total, List.append_assoc] using rest
  · have exhausted : HeapCalls.zipItem [.ref rowAddress, .ref belowAddress, .ref tailAddress]
        position heap = some (.ok none, heap) := by
      rw [readZip]
      by_cases inRow : position < row.length
      · have tailGone : below[position + 1]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [tailGone]
        cases row[position]? <;> cases below[position]? <;> rfl
      · rw [List.getElem?_eq_none_iff.mpr (by omega : row.length ≤ position)]
        rfl
    refine ⟨env, scratch, ?_⟩
    have done : (rowTotals row below).drop position = [] :=
      List.drop_eq_nil_iff.mpr (by simpa [ProjectEulerStatements.P18.rowTotals_length] using Nat.le_of_not_gt active)
    simpa [done] using HeapCalls.BlockContinues.zip_done (module := program) (env := env)
      (body := rowBody base.length) (otherwise := []) exhausted HeapCalls.BlockContinues.nil
termination_by min row.length (below.length - 1) - position
decreasing_by omega

private abbrev rowTarget : Expr := .tuple [.name "x", .name "y", .name "z"]
private abbrev rowSources : List Expr :=
  [.name "row", .name "below", .subscript (.name "below") (.slice (some (.constant (.int 1))) none none)]
private abbrev rowComprehension : Expr := .listCompTargets rowElement [(rowTarget, .zipIterable rowSources, [])]

private theorem rowComprehension.result (heap : Mutable.Heap) (env : HeapCalls.Env)
    (rowAddress belowAddress : Nat) (row below : List Int)
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (getBelow : heap[belowAddress]? = some (.list (encode below)))
    (localRow : env "row" = some (.ref rowAddress))
    (localBelow : env "below" = some (.ref belowAddress)) :
    ∃ scratch, HeapCalls.Evaluates program env rowComprehension heap (.ref (heap.length + 1))
      (workHeap (heap ++ [.list (encode below.tail)]) (rowTotals row below) scratch) := by
  let base := heap ++ [Mutable.Object.list (encode below.tail)]
  have rowBound : rowAddress < heap.length := (List.getElem?_eq_some_iff.mp getRow).choose
  have belowBound : belowAddress < heap.length := (List.getElem?_eq_some_iff.mp getBelow).choose
  have readRow : base[rowAddress]? = some (.list (encode row)) := by
    simpa [base, List.getElem?_append_left rowBound] using getRow
  have readBelow : base[belowAddress]? = some (.list (encode below)) := by
    simpa [base, List.getElem?_append_left belowBound] using getBelow
  have readTail : base[heap.length]? = some (.list (encode below.tail)) := by simp [base]
  have sliced : HeapCalls.Evaluates program env rowSources[2] heap (.ref heap.length) base := by
    apply HeapCalls.Evaluates.slice (.cons (.lookup localBelow) (.cons .constant (.cons .constant (.cons .constant .nil))))
    simpa [base, encode, List.drop_one] using Mutable.getSlice_list_suffix heap belowAddress (encode below) 1 getBelow
  have arguments : HeapCalls.Evaluates.Arguments program env rowSources heap
      [.ref rowAddress, .ref belowAddress, .ref heap.length] base :=
    .cons (.lookup localRow) (.cons (.lookup localBelow) (.cons sliced .nil))
  have captured : HeapCalls.zipSources [.ref rowAddress, .ref belowAddress, .ref heap.length] base =
      some (.ok [.ref rowAddress, .ref belowAddress, .ref heap.length], base) := by
    simp [HeapCalls.zipSources, List.mapM, List.mapM.loop, Mutable.sequence,
      readRow, readBelow, readTail, HeapCalls.sequenceSource, Except.map]
  let masked := HeapCalls.comprehensionTargetsEnv env [(rowTarget, .zipIterable rowSources, [])]
  obtain ⟨finalEnv, scratch, executed⟩ := rowLoop.result base [] row below []
    rowAddress belowAddress heap.length 0 masked readRow readBelow readTail
  refine ⟨scratch, ?_⟩
  have result := HeapCalls.Evaluates.list_comp_targets_zip arguments captured
    (by simpa [masked, workHeap, rowBody, HeapCalls.comprehensionTargetName,
      HeapCalls.comprehensionTargetBody, HeapCalls.comprehensionFilters, HeapCalls.comprehensionTargetsBody]
      using executed)
  simpa [rowComprehension, base, workHeap, List.append_assoc] using result

private abbrev rowGuard : Expr := .boolOp .or
  [.unaryOp .not (.name "row"), .compare (.builtinCall .len [.name "below"]) [(.lt, .constant (.int 2))]]

private theorem rowGuard.result (heap : Mutable.Heap) (env : HeapCalls.Env)
    (rowAddress belowAddress : Nat) (row below : List Int)
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (getBelow : heap[belowAddress]? = some (.list (encode below)))
    (localRow : env "row" = some (.ref rowAddress))
    (localBelow : env "below" = some (.ref belowAddress)) :
    HeapCalls.Evaluates program env rowGuard heap
      (.scalar (.bool (decide (row = [] ∨ below.length < 2)))) heap := by
  by_cases empty : row = []
  · simp only [empty, true_or, decide_true]
    apply HeapCalls.Evaluates.boolean_stop (flag := true) (middle := heap)
    · exact HeapCalls.Evaluates.unary (.lookup localRow)
        (by simp [HeapCalls.unary, Mutable.truth, getRow, empty, encode])
    · rfl
    · rfl
  · simp only [empty, false_or]
    apply HeapCalls.Evaluates.boolean_next (flag := false) (value := .scalar (.bool false)) (middle := heap)
    · exact HeapCalls.Evaluates.unary (.lookup localRow)
        (by simp [HeapCalls.unary, Mutable.truth, getRow, encode, empty])
    · rfl
    · rfl
    · apply HeapCalls.Evaluates.boolean_last (value := .scalar (.bool (decide (below.length < 2))))
      · apply HeapCalls.Evaluates.compare (av := .scalar (.int below.length)) (middle := heap)
        · exact HeapCalls.Evaluates.builtin (.cons (.lookup localBelow) .nil)
            (by simp [HeapCalls.primitive, Mutable.length, getBelow, encode])
        · exact .constant
        · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      · rfl

theorem max_row.result (heap : Mutable.Heap) (rowAddress belowAddress : Nat) (row below : List Int)
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (getBelow : heap[belowAddress]? = some (.list (encode below))) :
    ∃ extra address, HeapCalls.ReturnsValue program "max_row" [.ref rowAddress, .ref belowAddress]
      heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (encode (rowTotals row below))) := by
  let env := HeapCalls.argumentEnv
    [⟨"row", some (.subscript (.name "list") (.name "int")), none⟩,
      ⟨"below", some (.subscript (.name "list") (.name "int")), none⟩]
    [.ref rowAddress, .ref belowAddress]
  have guard := rowGuard.result heap env rowAddress belowAddress row below getRow getBelow rfl rfl
  by_cases stop : row = [] ∨ below.length < 2
  · have totals : rowTotals row below = [] := by
      apply List.length_eq_zero_iff.mp
      rw [ProjectEulerStatements.P18.rowTotals_length]
      rcases stop with empty | short
      · simp [empty]
      · have : below.length - 1 = 0 := by omega
        simp [this]
    refine ⟨[.list []], heap.length, ?_, ?_⟩
    · apply HeapCalls.BlockReturns.function rfl rfl
      apply HeapCalls.BlockReturns.branch (flag := true) (value := .scalar (.bool true)) (middle := heap)
        (by simpa only [stop, decide_true] using guard) rfl
      exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.list .nil)
    · simp [totals, encode]
  · obtain ⟨scratch, calculated⟩ := rowComprehension.result heap env rowAddress belowAddress row below
      getRow getBelow rfl rfl
    have executed : HeapCalls.ReturnsValue program "max_row" [.ref rowAddress, .ref belowAddress]
        heap (.ref (heap.length + 1))
        (workHeap (heap ++ [.list (encode below.tail)]) (rowTotals row below) scratch) := by
      apply HeapCalls.BlockReturns.function rfl rfl
      apply HeapCalls.BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := heap)
        (by simpa only [stop, decide_false] using guard) rfl
      exact HeapCalls.BlockReturns.return_value calculated
    refine ⟨[.list (encode below.tail), .list (encode (rowTotals row below))] ++ scratch, heap.length + 1, ?_, ?_⟩
    · simpa [workHeap, List.append_assoc] using executed
    · simp

theorem max_row.«Returns» (heap : Mutable.Heap) (rowAddress belowAddress : Nat) (_valid : heap.Valid)
    (rowType : Mutable.Value.HasType heap (.ref rowAddress) "list[int]")
    (belowType : Mutable.Value.HasType heap (.ref belowAddress) "list[int]") :
    (HeapCalls.call program "max_row" [.ref rowAddress, .ref belowAddress] heap).Returns := by
  obtain ⟨row, getRow⟩ := Mutable.Value.ints_of_hasType rowType
  obtain ⟨below, getBelow⟩ := Mutable.Value.ints_of_hasType belowType
  obtain ⟨extra, address, executed, _⟩ := max_row.result heap rowAddress belowAddress row below getRow getBelow
  exact executed.returns

theorem max_row.«Supported» (heap : Mutable.Heap) (rowAddress belowAddress : Nat) (valid : heap.Valid)
    (rowType : Mutable.Value.HasType heap (.ref rowAddress) "list[int]")
    (belowType : Mutable.Value.HasType heap (.ref belowAddress) "list[int]") :
    (HeapCalls.call program "max_row" [.ref rowAddress, .ref belowAddress] heap).Supported :=
  (max_row.«Returns» heap rowAddress belowAddress valid rowType belowType).supported

private theorem prefix_read (heap extra : Mutable.Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).choose]
  exact found

private abbrev triangleBody : List Stmt :=
  [.assign [.name "acc"] (.call (.name "max_row") [.name "row", .name "acc"])]

/-- Each row call extends the heap, retaining shared input rows and the captured iterator. -/
private theorem triangleLoop.result (heap : Mutable.Heap) (rows : List (Nat × List Int))
    (sequenceAddress position accAddress : Nat) (acc : List Int) (env : HeapCalls.Env)
    (getSequence : heap[sequenceAddress]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (getAcc : heap[accAddress]? = some (.list (encode acc)))
    (localAcc : env "acc" = some (.ref accAddress)) :
    ∃ finalEnv extra address, HeapCalls.BlockContinues program env
      [.sequenceStepLoop "row" (.ref sequenceAddress) position triangleBody []]
      heap finalEnv (heap ++ extra) ∧
      finalEnv "acc" = some (.ref address) ∧
      (heap ++ extra)[address]? = some (.list (encode
        ((rows.drop position).foldl (fun acc pair => rowTotals pair.2 acc) acc))) := by
  have sequence : Mutable.sequence (.ref sequenceAddress) heap =
      some (.ok (rows.map (fun pair => .ref pair.1)), heap) := by
    simp [Mutable.sequence, getSequence]
  by_cases active : position < rows.length
  · let pair := rows[position]
    let rowEnv := HeapCalls.setLocal env "row" (.ref pair.1)
    obtain ⟨extra, address, calculated, found⟩ := max_row.result heap pair.1 accAddress pair.2 acc
      (getRows pair (List.getElem_mem active)) getAcc
    let assigned := HeapCalls.setLocal rowEnv "acc" (.ref address)
    have called : HeapCalls.BlockContinues program rowEnv triangleBody heap assigned (heap ++ extra) := by
      apply HeapCalls.BlockContinues.assign
      exact HeapCalls.Evaluates.call (.cons (.lookup rfl)
        (.cons (.lookup (by simpa [rowEnv, HeapCalls.setLocal] using localAcc)) .nil)) calculated
    obtain ⟨finalEnv, more, finalAddress, continued, finalAcc, finalRow⟩ :=
      triangleLoop.result (heap ++ extra) rows sequenceAddress (position + 1) address
        (rowTotals pair.2 acc) assigned (prefix_read heap extra _ _ getSequence)
        (fun item member => prefix_read heap extra _ _ (getRows item member)) found rfl
    refine ⟨finalEnv, extra ++ more, finalAddress, ?_, finalAcc, ?_⟩
    · apply HeapCalls.BlockContinues.sequence_step (source := .ref sequenceAddress) (heap := heap)
        (position := position) (value := .ref pair.1) sequence
        (by simp [List.getElem?_eq_getElem active, pair])
      simpa [triangleBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.append_assoc] using called.append continued
    · rw [List.drop_eq_getElem_cons active, List.foldl_cons]
      simpa only [List.append_assoc] using finalRow
  · have done : rows.drop position = [] := List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt active)
    refine ⟨env, [], accAddress, ?_, localAcc, ?_⟩
    · simpa using HeapCalls.BlockContinues.sequence_done (module := program) (env := env)
        (source := .ref sequenceAddress) (position := position) (body := triangleBody) (otherwise := [])
        sequence (by simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt active)]) HeapCalls.BlockContinues.nil
    · simpa [done] using getAcc
termination_by rows.length - position
decreasing_by omega

private theorem firstOrZero.result (heap : Mutable.Heap) (env : HeapCalls.Env)
    (address : Nat) (values : List Int)
    (found : heap[address]? = some (.list (encode values)))
    (getLocal : env "acc" = some (.ref address)) :
    HeapCalls.Evaluates program env
      (.ifExp (.name "acc") (.subscript (.name "acc") (.constant (.int 0))) (.constant (.int 0)))
      heap (.scalar (.int (values.headD 0))) heap := by
  cases values with
  | nil =>
      exact HeapCalls.Evaluates.conditional (flag := false) (.lookup getLocal)
        (by simp [Mutable.truth, found, encode]) .constant
  | cons value rest =>
      apply HeapCalls.Evaluates.conditional (flag := true) (.lookup getLocal)
        (by simp [Mutable.truth, found, encode])
      apply HeapCalls.Evaluates.subscript (by intros a b c impossible; cases impossible) (.lookup getLocal) .constant
      simpa [encode] using Mutable.getItem_list heap address 0 (encode (value :: rest)) found (by simp [encode])

theorem naive.result (heap : Mutable.Heap) (address : Nat) (rows : List (Nat × List Int))
    (getTriangle : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ∃ extra, HeapCalls.ReturnsValue program "naive" [.ref address] heap
      (.scalar (.int ((ProjectEulerStatements.P18.reduceRowValues (rows.map Prod.snd)).headD 0)))
      (heap ++ extra) := by
  let initial := HeapCalls.argumentEnv
    [⟨"tri", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩]
    [.ref address]
  let env := HeapCalls.setLocal initial "rows" (.ref heap.length)
  let base := heap ++ [Mutable.Object.list (rows.reverse.map (fun pair => .ref pair.1))]
  have reversed : HeapCalls.Evaluates program initial (.reversedList (.name "tri")) heap (.ref heap.length) base := by
    simpa [base, List.map_reverse] using HeapCalls.Evaluates.reversed_list
      (module := program) (globals := []) (HeapCalls.Evaluates.lookup (env := initial) (name := "tri") rfl) getTriangle
  have foundRows : base[heap.length]? = some (.list (rows.reverse.map (fun pair => .ref pair.1))) := by simp [base]
  cases backwards : rows.reverse with
  | nil =>
      refine ⟨[.list []], ?_⟩
      have computed : ProjectEulerStatements.P18.reduceRowValues (rows.map Prod.snd) = [] := by
        simp only [ProjectEulerStatements.P18.reduceRowValues, ← List.map_reverse, backwards, List.map_nil]
      rw [computed]
      apply HeapCalls.BlockReturns.function rfl rfl
      apply HeapCalls.BlockReturns.assign (value := .ref heap.length) (middle := base) reversed
      apply HeapCalls.BlockReturns.branch (flag := true) (value := .scalar (.bool true)) (middle := base)
      · exact HeapCalls.Evaluates.unary (.lookup rfl)
          (by simp [HeapCalls.unary, Mutable.truth, foundRows, backwards])
      · rfl
      · simpa [base, backwards] using HeapCalls.BlockReturns.return_value
          (module := program) (env := env) (HeapCalls.Evaluates.constant (heap := base) (value := .int 0))
  | cons bottom rest =>
      let accEnv := HeapCalls.setLocal env "acc" (.ref bottom.1)
      let slicedHeap := base ++ [Mutable.Object.list (rest.map (fun pair => .ref pair.1))]
      have readBottom : base[bottom.1]? = some (.list (encode bottom.2)) :=
        prefix_read heap _ _ _ (getRows bottom (List.mem_reverse.mp (by rw [backwards]; exact List.mem_cons_self)))
      have sliced : HeapCalls.Evaluates program accEnv
          (.subscript (.name "rows") (.slice (some (.constant (.int 1))) none none))
          base (.ref base.length) slicedHeap := by
        apply HeapCalls.Evaluates.slice (.cons (.lookup rfl) (.cons .constant (.cons .constant (.cons .constant .nil))))
        simpa [slicedHeap, backwards] using Mutable.getSlice_list_suffix base heap.length
          (rows.reverse.map (fun pair => .ref pair.1)) 1 foundRows
      have sliceFound : slicedHeap[base.length]? = some (.list (rest.map (fun pair => .ref pair.1))) := by
        simp [slicedHeap]
      obtain ⟨finalEnv, extra, finalAddress, loop, localAcc, finalRow⟩ := triangleLoop.result slicedHeap rest
        base.length 0 bottom.1 bottom.2 accEnv sliceFound
        (fun pair member => prefix_read base _ _ _ (prefix_read heap _ _ _
          (getRows pair (List.mem_reverse.mp (by rw [backwards]; exact List.mem_cons_of_mem bottom member)))))
        (prefix_read base _ _ _ readBottom) rfl
      have executedLoop : HeapCalls.BlockContinues program accEnv
          [.forIn (.name "row") (.subscript (.name "rows") (.slice (some (.constant (.int 1))) none none))
            triangleBody []] base finalEnv (slicedHeap ++ extra) :=
        HeapCalls.BlockContinues.for_sequence (items := rest.map (fun pair => .ref pair.1))
          (by intros expressions impossible; cases impossible) sliced
          (by simp [Mutable.sequence, sliceFound]) loop
      have finish := firstOrZero.result (slicedHeap ++ extra) finalEnv finalAddress
        (rest.foldl (fun acc pair => rowTotals pair.2 acc) bottom.2) (by simpa using finalRow) localAcc
      have computed : ProjectEulerStatements.P18.reduceRowValues (rows.map Prod.snd) =
          rest.foldl (fun acc pair => rowTotals pair.2 acc) bottom.2 := by
        simp only [ProjectEulerStatements.P18.reduceRowValues, ← List.map_reverse, backwards, List.map_cons, List.foldl_map]
      have executed : HeapCalls.ReturnsValue program "naive" [.ref address] heap
          (.scalar (.int ((ProjectEulerStatements.P18.reduceRowValues (rows.map Prod.snd)).headD 0)))
          (slicedHeap ++ extra) := by
        apply HeapCalls.BlockReturns.function rfl rfl
        apply HeapCalls.BlockReturns.assign reversed
        apply HeapCalls.BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := base)
        · exact HeapCalls.Evaluates.unary (.lookup rfl)
            (by simp [HeapCalls.unary, Mutable.truth, foundRows, backwards])
        · rfl
        · apply HeapCalls.BlockReturns.assign (value := .ref bottom.1) (middle := base)
          · apply HeapCalls.Evaluates.subscript (by intros a b c impossible; cases impossible) (.lookup rfl) .constant
            simpa [backwards] using Mutable.getItem_list base heap.length 0
              (rows.reverse.map (fun pair => .ref pair.1)) foundRows (by simp [backwards])
          · simpa only [computed] using executedLoop.returns (HeapCalls.BlockReturns.return_value finish)
      refine ⟨[.list (rows.reverse.map (fun pair => .ref pair.1)), .list (rest.map (fun pair => .ref pair.1))] ++ extra, ?_⟩
      simpa [base, slicedHeap, List.append_assoc] using executed

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "naive" [.ref address] heap).Returns := by
  classical
  obtain ⟨addresses, getTriangle, rowTypes⟩ := Mutable.Value.lists_of_hasType typed
  have decoded : ∀ row ∈ addresses, ∃ values : List Int, heap[row]? = some (.list (encode values)) :=
    fun row member => Mutable.Value.ints_of_hasType (rowTypes row member)
  choose values contents using decoded
  let rows := addresses.attach.map (fun entry => (entry.val, values entry.val entry.property))
  have sameAddresses : rows.map (fun pair => Mutable.Value.ref pair.1) = addresses.map Mutable.Value.ref := by
    simp [rows, List.map_map]
  have reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)) := by
    intro pair member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact contents entry.val entry.property
  obtain ⟨extra, executed⟩ := naive.result heap address rows (by simpa [sameAddresses] using getTriangle) reads
  exact executed.returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]") :
    (HeapCalls.call program "naive" [.ref address] heap).Supported :=
  (naive.«Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p18
