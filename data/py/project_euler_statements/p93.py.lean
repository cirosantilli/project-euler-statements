import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Operations

namespace data.«project-euler-statements».data.py.project_euler_statements.p93
open FormalSW.PyAst ProjectEulerSolutions.RationalPair

theorem eval_ops_source (a b : Pair) (left right : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    heap[left]? = some (Heap.object a) → heap[right]? = some (Heap.object b) →
      eval_ops.Verified a b left right heap globals :=
  eval_ops.verified a b left right heap globals

end data.«project-euler-statements».data.py.project_euler_statements.p93
