import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Row

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

theorem relax_up.result (heap : Mutable.Heap) (costAddress colAddress : Nat) (cost col : List Int)
    (getCost : heap[costAddress]? = some (.list (encode cost)))
    (getColumn : heap[colAddress]? = some (.list (encode col))) (same : cost.length = col.length) :
    ∃ extra address, ReturnsValue program "relax_up" [.ref costAddress, .ref colAddress] heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (encode (relaxUp cost col))) := by
  let args : List Arg :=
    [⟨"cost", some (.subscript (.name "list") (.name "int")), none⟩,
     ⟨"col", some (.subscript (.name "list") (.name "int")), none⟩]
  let entry := argumentEnv args [.ref costAddress, .ref colAddress]
  let firstHeap := heap ++ [.list (encode cost.reverse)]
  let secondHeap := firstHeap ++ [.list (encode col.reverse)]
  have first : Evaluates program entry (.reversedList (.name "cost")) heap (.ref heap.length) firstHeap := by
    simpa [firstHeap, encode] using (Evaluates.reversed_list (module := program) (env := entry) (Evaluates.lookup rfl) getCost)
  have columnKept : firstHeap[colAddress]? = some (.list (encode col)) := by
    unfold firstHeap
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getColumn).1]
    exact getColumn
  have second : Evaluates program entry (.reversedList (.name "col")) firstHeap (.ref firstHeap.length) secondHeap := by
    simpa [secondHeap, encode] using (Evaluates.reversed_list (module := program) (env := entry) (Evaluates.lookup rfl) columnKept)
  have costFound : secondHeap[heap.length]? = some (.list (encode cost.reverse)) := by
    simp [secondHeap, firstHeap, List.append_assoc]
  have colFound : secondHeap[firstHeap.length]? = some (.list (encode col.reverse)) := by simp [secondHeap]
  obtain ⟨extra, address, returned, resultFound⟩ := relax_down.result secondHeap heap.length firstHeap.length cost.reverse col.reverse
    costFound colFound (by simpa using same)
  have called : Evaluates program entry (.call (.name "relax_down")
      [.reversedList (.name "cost"), .reversedList (.name "col")]) heap (.ref address) (secondHeap ++ extra) :=
    Evaluates.call (.cons first (.cons second .nil)) returned
  have reversed := Evaluates.reversed_list called resultFound
  refine ⟨[.list (encode cost.reverse), .list (encode col.reverse)] ++ extra ++ [.list (encode (relaxUp cost col))],
    (secondHeap ++ extra).length, ?_, ?_⟩
  · apply BlockReturns.function (args := args) rfl rfl
    apply BlockReturns.return_value
    simpa [secondHeap, firstHeap, encode, relaxUp, List.append_assoc] using reversed
  · have equal : heap ++ ([.list (encode cost.reverse), .list (encode col.reverse)] ++ extra ++ [.list (encode (relaxUp cost col))]) =
        (secondHeap ++ extra) ++ [.list (encode (relaxUp cost col))] := by simp [secondHeap, firstHeap, List.append_assoc]
    rw [equal]
    simp

end data.«project-euler-statements».data.py.project_euler_statements.p82
