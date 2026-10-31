import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».ShortestPath

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (_shape : HeapCalls.Condition program (matrixEnv address) P83Ast.requires_naive_0 heap)
    (_costs : HeapCalls.Condition program (matrixEnv address) P83Ast.requires_naive_1 heap) :
    (HeapCalls.call program "naive" [.ref address] heap).Returns := by
  obtain ⟨rows, found, reads⟩ := decode_rows heap address typed
  obtain ⟨_, returned⟩ := naive.result heap address rows found reads
  exact returned.returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (shape : HeapCalls.Condition program (matrixEnv address) P83Ast.requires_naive_0 heap)
    (costs : HeapCalls.Condition program (matrixEnv address) P83Ast.requires_naive_1 heap) :
    (HeapCalls.call program "naive" [.ref address] heap).Supported :=
  (naive.«Returns» heap address valid typed shape costs).supported

end data.«project-euler-statements».data.py.project_euler_statements.p83
