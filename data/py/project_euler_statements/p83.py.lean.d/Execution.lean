import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Iteration

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows arguments)
open ProjectEulerSolutions.TriangleBufferCalls
open ProjectEulerStatements.P83 (getD2)
set_option Elab.async false

theorem min_path.result (heap : Mutable.Heap) (address : Nat) (matrix : MatrixRows)
    (found : heap[address]? = some (.list (matrix.map (fun row => .ref row.1))))
    (reads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2))) :
    ∃ extra, ReturnsValue program "min_path" [.ref address] heap
      (number (ProjectEulerStatements.P83.naive (matrix.map Prod.snd))) (heap ++ extra) := by
  let entry := argumentEnv arguments [.ref address]
  let base := heap ++ [dimensionObject matrix]
  let ready := assignNames entry ["rows", "cols"] [number matrix.length, number ((matrix.map Prod.snd).headD []).length]
  have kept (target : Nat) (object : Mutable.Object) (read : heap[target]? = some object) : base[target]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
    exact read
  have dimensions : Evaluates program entry (.call (.name "dims") [.name "matrix"]) heap (.ref heap.length) base :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (dims.result heap address matrix found reads)
  obtain ⟨initExtra, initAddress, initial, initialized, initFound, initReads, initData⟩ :=
    init_dist.complete base address matrix (kept _ _ found) (fun row member => kept _ _ (reads row member))
  have initialization : Evaluates program ready (.call (.name "init_dist") [.name "matrix"]) base
      (.ref initAddress) (base ++ initExtra) := Evaluates.call (.cons (Evaluates.lookup rfl) .nil) initialized
  have initKept (target : Nat) (object : Mutable.Object) (read : base[target]? = some object) :
      (base ++ initExtra)[target]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
    exact read
  obtain ⟨iterExtra, iterAddress, result, iterated, resultFound, resultReads, resultData⟩ :=
    iterate.result (base ++ initExtra) address initAddress matrix initial
      (initKept _ _ (kept _ _ found)) (fun row member => initKept _ _ (kept _ _ (reads row member))) initFound initReads
  let finalHeap := (base ++ initExtra) ++ iterExtra
  have traversal : Evaluates program ready
      (.call (.name "iterate") [.name "matrix", .call (.name "init_dist") [.name "matrix"]]) base
      (.ref iterAddress) finalHeap := Evaluates.call (.cons (Evaluates.lookup rfl) (.cons initialization .nil)) iterated
  have rowIndex : Evaluates program ready (.binOp (.name "rows") .sub (.constant (.int 1))) finalHeap
      (number ((matrix.length : Int) - 1)) finalHeap := Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl
  have colIndex : Evaluates program ready (.binOp (.name "cols") .sub (.constant (.int 1))) finalHeap
      (number ((((matrix.map Prod.snd).headD []).length : Int) - 1)) finalHeap :=
    Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl
  have output := get_d2.result finalHeap iterAddress result ((matrix.length : Int) - 1)
    ((((matrix.map Prod.snd).headD []).length : Int) - 1) resultFound resultReads
  have answer : getD2 (result.map Prod.snd) ((matrix.length : Int) - 1)
      ((((matrix.map Prod.snd).headD []).length : Int) - 1) = ProjectEulerStatements.P83.naive (matrix.map Prod.snd) := by
    rw [resultData, initData]
    simp only [ProjectEulerStatements.P83.naive, ProjectEulerStatements.P83.minPath,
      ProjectEulerStatements.P83.dims, List.length_map]
  rw [answer] at output
  refine ⟨[dimensionObject matrix] ++ initExtra ++ iterExtra, ?_⟩
  apply BlockReturns.function (args := arguments) rfl rfl
  apply BlockReturns.unpack (afterUnpack := base) (names := ["rows", "cols"]) rfl dimensions
    (items := [number matrix.length, number ((matrix.map Prod.snd).headD []).length])
    (by simp [Mutable.sequence, base, dimensionObject]) rfl
  have returned := BlockReturns.return_value (rest := [])
    (Evaluates.call (.cons traversal (.cons rowIndex (.cons colIndex .nil))) output)
  simpa only [finalHeap, base, List.append_assoc] using returned

theorem naive.result (heap : Mutable.Heap) (address : Nat) (matrix : MatrixRows)
    (found : heap[address]? = some (.list (matrix.map (fun row => .ref row.1))))
    (reads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2))) :
    ∃ extra, ReturnsValue program "naive" [.ref address] heap
      (number (ProjectEulerStatements.P83.naive (matrix.map Prod.snd))) (heap ++ extra) := by
  obtain ⟨extra, executed⟩ := min_path.result heap address matrix found reads
  refine ⟨extra, ?_⟩
  apply BlockReturns.function (args := arguments) rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) executed)

end data.«project-euler-statements».data.py.project_euler_statements.p83
