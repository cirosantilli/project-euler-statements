import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Columns
import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Finish

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

def columnPairs (base : Mutable.Heap) (rows : MatrixRows) (count : Nat) : MatrixRows :=
  (List.range count).map (fun index => (base.length + 1 + index, getCol (rows.map Prod.snd) index))

theorem column_found (base : Mutable.Heap) (rows : MatrixRows) (count index : Nat) (inside : index < count) :
    (columnsHeap base rows count)[base.length + 1 + index]? = some (.list (encode (getCol (rows.map Prod.snd) index))) := by
  unfold columnsHeap
  rw [List.getElem?_append_right (by simp)]
  have item : (List.range count)[index]? = some index := by
    rw [List.getElem?_eq_getElem (by simpa using inside)]
    simp
  simp [item, encode, ProjectEulerSolutions.TriangleBufferCalls.encode]

theorem min_path.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (getMatrix : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ∃ extra, ReturnsValue program "min_path" [.ref address] heap
      (number (ProjectEulerStatements.P82.naive (rows.map Prod.snd))) (heap ++ extra) := by
  let entry := argumentEnv arguments [.ref address]
  have tested : Evaluates program entry (.unaryOp .not (.name "matrix")) heap
      (.scalar (.bool (decide (rows = [])))) heap :=
    Evaluates.unary (Evaluates.lookup rfl)
      (by simp [HeapCalls.unary, Mutable.truth, getMatrix]; cases rows <;> rfl)
  cases rows with
  | nil =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil, List.map_nil, ProjectEulerStatements.P82.naive, minPath, List.headD_nil, List.length_nil, List.range_zero]
      apply BlockReturns.function (args := arguments) rfl rfl
      apply BlockReturns.branch (flag := true) tested rfl
      exact BlockReturns.return_value Evaluates.constant
  | cons first rest =>
      let pairs := columnPairs heap (first :: rest) first.2.length
      let state := columnsHeap heap (first :: rest) first.2.length
      let ready := setLocal entry "cols" (.ref heap.length)
      have allocated := columns_allocation heap entry address first rest getMatrix getRows rfl
      have source : state[heap.length]? = some (.list (pairs.map (fun pair => .ref pair.1))) := by
        simp [state, pairs, columnsHeap, columnPairs, columnRefs, List.append_assoc, List.map_map, Function.comp_def]
      have reads : ∀ pair ∈ pairs, state[pair.1]? = some (.list (encode pair.2)) := by
        intro pair member
        simp only [pairs, columnPairs, List.mem_map] at member
        obtain ⟨index, indexBound, rfl⟩ := member
        exact column_found heap (first :: rest) first.2.length index (List.mem_range.mp indexBound)
      have shape : ∀ pair ∈ pairs, pair.2.length = (first :: rest).length := by
        intro pair member
        simp only [pairs, columnPairs, List.mem_map] at member
        obtain ⟨index, _, rfl⟩ := member
        simp
      obtain ⟨extra, finish⟩ := finish_columns state ready heap.length (first :: rest).length pairs source reads shape rfl
      have answer : columnsValue pairs = ProjectEulerStatements.P82.naive ((first :: rest).map Prod.snd) := by
        simp [columnsValue, pairs, columnPairs, ProjectEulerStatements.P82.naive, minPath, List.map_map, Function.comp_def]
        rfl
      rw [answer] at finish
      refine ⟨([.list (columnRefs heap first.2.length)] ++
        (List.range first.2.length).map (fun index => .list (encode (getCol ((first :: rest).map Prod.snd) index)))) ++ extra, ?_⟩
      apply BlockReturns.function (args := arguments) rfl rfl
      apply BlockReturns.branch (flag := false) tested rfl
      apply BlockReturns.assign allocated
      simpa only [state, columnsHeap, List.append_assoc] using finish

theorem naive.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (getMatrix : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ∃ extra, ReturnsValue program "naive" [.ref address] heap
      (number (ProjectEulerStatements.P82.naive (rows.map Prod.snd))) (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := min_path.result heap address rows getMatrix getRows
  refine ⟨extra, ?_⟩
  apply BlockReturns.function (args := arguments) rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) returned)

end data.«project-euler-statements».data.py.project_euler_statements.p82
