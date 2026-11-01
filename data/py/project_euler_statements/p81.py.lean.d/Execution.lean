import data.«project-euler-statements».data.py.project_euler_statements.«p81.py.lean.d».Rows

namespace data.«project-euler-statements».data.py.project_euler_statements.p81
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P81
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev firstFor : Stmt := .forIn (.name "x") (.subscript (.name "matrix") (.constant (.int 0))) prefixBody []
abbrev rowsFor : Stmt := .forIn (.name "row")
  (.subscript (.name "matrix") (.slice (some (.constant (.int 1))) none none)) rowsBody []

theorem min_path.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (getMatrix : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) (shape : Shape rows) :
    ∃ extra, ReturnsValue program "min_path" [.ref address] heap
      (number (ProjectEulerStatements.P81.naive (rows.map Prod.snd))) (heap ++ extra) := by
  let entry := argumentEnv arguments [.ref address]
  have tested : Evaluates program entry (.unaryOp .not (.name "matrix")) heap
      (.scalar (.bool (decide (rows = [])))) heap :=
    Evaluates.unary (Evaluates.lookup rfl)
      (by simp [HeapCalls.unary, Mutable.truth, getMatrix]; cases rows <;> rfl)
  cases rows with
  | nil =>
      refine ⟨[], ?_⟩
      apply BlockReturns.function (args := arguments) rfl rfl
      apply BlockReturns.branch (flag := true) tested rfl
      simpa [ProjectEulerStatements.P81.naive, minPath, number] using
        (BlockReturns.return_value (module := program) (env := entry) (heap := heap) Evaluates.constant
          : BlockReturns program entry (.return (.constant (.int 0)) :: _) heap (number 0) heap)
  | cons first rest =>
      let initialized := setLocal entry "init" (.ref heap.length)
      have firstRead := getRows first (by simp)
      obtain ⟨after, loop, kept⟩ := prefixLoop_result heap initialized first.1 0 first.2 [] firstRead rfl
      have localMatrix : after "matrix" = some (.ref address) := by rw [kept "matrix" (by decide)]; rfl
      have localInit : after "init" = some (.ref heap.length) := by rw [kept "init" (by decide)]; rfl
      let initial := firstRow first.2
      let base := prefixHeap heap initial
      have prefixDone : BlockContinues program initialized [firstFor] (prefixHeap heap []) after base := by
        have foundMatrix : (prefixHeap heap [])[address]? = some (.list ((first :: rest).map (fun pair => .ref pair.1))) := by
          unfold prefixHeap
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getMatrix).1]
          exact getMatrix
        have foundFirst : (prefixHeap heap [])[first.1]? = some (.list (encode first.2)) := by
          unfold prefixHeap
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp firstRead).1]
          exact firstRead
        apply BlockContinues.for_sequence (value := .ref first.1) (middle := prefixHeap heap []) (items := encode first.2) (by intros expressions impossible; cases impossible)
        · apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup rfl) Evaluates.constant
          simp [Mutable.getItem, Mutable.index, foundMatrix, Except.map]
        · simp [Mutable.sequence, foundFirst]
        · simpa [base, initial, firstRow] using loop
      let ready := setLocal after "final" (.ref heap.length)
      let remaining := rest.map (fun pair => Mutable.Value.ref pair.1)
      let sliced := base ++ [.list remaining]
      have baseMatrix : base[address]? = some (.list ((first :: rest).map (fun pair => .ref pair.1))) := by
        unfold base prefixHeap
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getMatrix).1]
        exact getMatrix
      have slice : Evaluates program ready (.subscript (.name "matrix") (.slice (some (.constant (.int 1))) none none))
          base (.ref base.length) sliced := by
        apply Evaluates.slice (.cons (Evaluates.lookup (by simpa [ready, setLocal] using localMatrix))
          (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
        simpa [sliced, remaining] using Mutable.getSlice_list_suffix base address
          ((first :: rest).map (fun pair => .ref pair.1)) 1 baseMatrix
      have allRows : ∀ pair ∈ rest, sliced[pair.1]? = some (.list (encode pair.2)) := by
        intro pair member
        have found := getRows pair (by simp [member])
        simp only [sliced, base, prefixHeap, List.append_assoc]
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
        exact found
      have rectangular : ∀ pair ∈ rest, pair.2.length = first.2.length := by
        intro pair member
        obtain ⟨index, inside, equal⟩ := List.mem_iff_getElem.mp (show pair ∈ first :: rest by simp [member])
        rw [← equal]
        exact shape index inside
      have initFound : sliced[heap.length]? = some (.list (encode initial)) := by
        simp [sliced, base, prefixHeap, List.append_assoc]
      have sourceFound : sliced[base.length]? = some (.list remaining) := by simp [sliced]
      obtain ⟨extra, rowsDone⟩ := rowsLoop_result sliced ready base.length 0 heap.length first.2.length rest initial
        sourceFound allRows rectangular (by simp [initial, firstRow]) initFound rfl
      refine ⟨[.list (encode initial), .list remaining] ++ extra, ?_⟩
      apply BlockReturns.function (args := arguments) rfl rfl
      apply BlockReturns.branch (flag := false) tested rfl
      apply BlockReturns.assign (value := .ref heap.length) (Evaluates.list .nil)
      have tail : BlockReturns program after [.assign [.name "final"] (.name "init"), rowsFor, pathReturn]
          base (number (ProjectEulerStatements.P81.naive ((first :: rest).map Prod.snd))) (sliced ++ extra) := by
        apply BlockReturns.assign (Evaluates.lookup localInit)
        apply BlockReturns.for_sequence (items := remaining) (by intros expressions impossible; cases impossible) slice
          (by simp [Mutable.sequence, sourceFound])
        simpa [ProjectEulerStatements.P81.naive, minPath, initial] using rowsDone
      simpa [firstFor, rowsFor, prefixHeap, sliced, base, List.append_assoc] using prefixDone.returns tail

theorem naive.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (getMatrix : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) (shape : Shape rows) :
    ∃ extra, ReturnsValue program "naive" [.ref address] heap
      (number (ProjectEulerStatements.P81.naive (rows.map Prod.snd))) (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := min_path.result heap address rows getMatrix getRows shape
  refine ⟨extra, ?_⟩
  apply BlockReturns.function (args := arguments) rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) returned)

end data.«project-euler-statements».data.py.project_euler_statements.p81
