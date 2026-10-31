import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».InitialRow
import ProjectEulerSolutions.Lib.MatrixRangeCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RectangularMatrixCalls
open ProjectEulerSolutions.TriangleBufferCalls (number)
open ProjectEulerSolutions.MatrixRangeCollection
open ProjectEulerStatements.P83 (bigVal initDist)
set_option Elab.async false

abbrev initialMatrixExpression : Expr := .listComp initialRowExpression [("r", .call (.name "range") [.name "rows"], [])]
def dimensionObject (rows : MatrixRows) : Mutable.Object :=
  .tuple [number rows.length, number ((rows.map Prod.snd).headD []).length]
def initialHeap (heap : Mutable.Heap) (rows : MatrixRows) : Mutable.Heap :=
  matrixHeap (heap ++ [dimensionObject rows]) (initialRow (rows.map Prod.snd)) rows.length

theorem initial_matrix_allocation (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (localMatrix : env "matrix" = some (.ref address)) (localHeight : env "rows" = some (number rows.length))
    (localWidth : env "cols" = some (number ((rows.map Prod.snd).headD []).length))
    (localBound : env "big" = some (number (bigVal (rows.map Prod.snd)))) :
    Evaluates program env initialMatrixExpression heap (.ref heap.length)
      (matrixHeap heap (initialRow (rows.map Prod.snd)) rows.length) := by
  apply collect (evaluated := .cons (Evaluates.lookup localHeight) .nil) (bounds := rfl)
  intro index inside
  exact initial_row_allocation _ _ address index rows
    (prefix_found heap _ index address _ found)
    (fun pair member => prefix_found heap _ index pair.1 _ (reads pair member))
    (by simpa [setLocal, comprehensionEnv] using localMatrix) rfl
    (by simpa [setLocal, comprehensionEnv] using localWidth)
    (by simpa [setLocal, comprehensionEnv] using localBound)

theorem init_dist.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ReturnsValue program "init_dist" [.ref address] heap (.ref (heap.length + 1)) (initialHeap heap rows) := by
  let entry := argumentEnv arguments [.ref address]
  let base := heap ++ [dimensionObject rows]
  let sized := assignNames entry ["rows", "cols"] [number rows.length, number ((rows.map Prod.snd).headD []).length]
  let ready := setLocal sized "big" (number (bigVal (rows.map Prod.snd)))
  have kept (target : Nat) (object : Mutable.Object) (read : heap[target]? = some object) : base[target]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
    exact read
  have dimensions : Evaluates program entry (.call (.name "dims") [.name "matrix"]) heap (.ref heap.length) base :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (dims.result heap address rows found reads)
  have bound : Evaluates program sized (.call (.name "big_val") [.name "matrix"]) base
      (number (bigVal (rows.map Prod.snd))) base :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      (big_val.result base address rows (kept _ _ found) (fun pair member => kept _ _ (reads pair member)))
  have allocated := initial_matrix_allocation base ready address rows (kept _ _ found)
    (fun pair member => kept _ _ (reads pair member)) rfl rfl rfl rfl
  apply BlockReturns.function (args := arguments) rfl rfl
  apply BlockReturns.unpack (afterUnpack := base) (names := ["rows", "cols"]) rfl dimensions
    (items := [number rows.length, number ((rows.map Prod.snd).headD []).length])
    (by simp [Mutable.sequence, base, dimensionObject]) rfl
  apply BlockReturns.assign bound
  simpa only [base, List.length_append, List.length_singleton] using BlockReturns.return_value allocated

theorem init_dist.complete (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ∃ (extra : Mutable.Heap) (resultAddress : Nat) (resultRows : MatrixRows),
      ReturnsValue program "init_dist" [.ref address] heap (.ref resultAddress) (heap ++ extra) ∧
      (heap ++ extra)[resultAddress]? = some (.list (resultRows.map (fun pair => .ref pair.1))) ∧
      (∀ pair ∈ resultRows, (heap ++ extra)[pair.1]? = some (.list (encode pair.2))) ∧
      resultRows.map Prod.snd = initDist (rows.map Prod.snd) := by
  let base := heap ++ [dimensionObject rows]
  let values := initialRow (rows.map Prod.snd)
  refine ⟨[dimensionObject rows, .list (rowRefs base rows.length)] ++
    (List.range rows.length).map (fun index => .list (encode (values index))),
    heap.length + 1, rowPairs base values rows.length, ?_, ?_, ?_, ?_⟩
  · simpa only [initialHeap, matrixHeap, List.append_assoc, List.singleton_append] using init_dist.result heap address rows found reads
  · simpa only [matrixHeap, base, List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using
      matrix_found base values rows.length
  · simpa only [matrixHeap, base, List.append_assoc, List.singleton_append] using rows_found base values rows.length
  · simp [rowPairs, values, initialRow, initDist, ProjectEulerStatements.P83.dims, List.map_map, Function.comp_def]

end data.«project-euler-statements».data.py.project_euler_statements.p83
