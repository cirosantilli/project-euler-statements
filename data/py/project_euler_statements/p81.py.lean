import data.«project-euler-statements».data.py.project_euler_statements.«p81.py.lean.d».Execution

namespace data.«project-euler-statements».data.py.project_euler_statements.p81
open FormalSW.PyAst ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (requires : HeapCalls.Condition program (matrixEnv address) P81Ast.requires_naive_0 heap) :
    (HeapCalls.call program "naive" [.ref address] heap).Returns := by
  obtain ⟨rows, found, reads, shape, _⟩ := domain_of_condition shape_source heap address typed requires
  obtain ⟨_, returned⟩ := naive.result heap address rows found reads shape
  exact returned.returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[list[int]]")
    (requires : HeapCalls.Condition program (matrixEnv address) P81Ast.requires_naive_0 heap) :
    (HeapCalls.call program "naive" [.ref address] heap).Supported :=
  (naive.«Returns» heap address valid typed requires).supported

end data.«project-euler-statements».data.py.project_euler_statements.p81
