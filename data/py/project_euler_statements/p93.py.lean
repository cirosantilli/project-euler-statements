import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Search

namespace data.«project-euler-statements».data.py.project_euler_statements.p93
open FormalSW.PyAst ProjectEulerSolutions.RationalPair

theorem eval_ops_source (a b : Pair) (left right : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    heap[left]? = some (Heap.object a) → heap[right]? = some (Heap.object b) →
      eval_ops.Verified a b left right heap globals :=
  eval_ops.verified a b left right heap globals

theorem all_results_source (xs : List Int) (address : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    heap[address]? = some (.tuple (xs.map Heap.number)) → all_results.Computed xs address heap globals :=
  all_results.result xs heap address globals

theorem consecutive_for_digits_source (xs : List Int) (address : Nat)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    heap[address]? = some (.tuple (xs.map Heap.number)) →
      ∃ extra, HeapCalls.ReturnsValue P93Ast.module "consecutive_for_digits" [.ref address] heap
        (Heap.number (consecutive_for_digits.runLength xs)) (heap ++ extra) globals :=
  consecutive_for_digits.result xs heap address globals

theorem naive_source (bound : Int) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    naive.Verified bound heap globals := naive.result bound heap globals

theorem naive.«Returns» (max_digit : Int) :
    (HeapCalls.call P93Ast.module "naive" [Heap.number max_digit] []).Returns := by
  obtain ⟨_, _, returned, _⟩ := naive.result max_digit [] []
  exact returned.returns

theorem naive.«Supported» (max_digit : Int) :
    (HeapCalls.call P93Ast.module "naive" [Heap.number max_digit] []).Supported :=
  (naive.«Returns» max_digit).supported

theorem naive.default_returns : (HeapCalls.call P93Ast.module "naive" [] []).Returns := by
  obtain ⟨_, _, returned, _⟩ := naive.default_result [] []
  exact returned.returns

theorem consecutive_count.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P93Ast.module "consecutive_count" [.ref address] heap).Returns := by
  obtain ⟨xs, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (consecutive_count.result xs heap address [] found).returns

theorem consecutive_count.«ReturnType» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P93Ast.module "consecutive_count" [.ref address] heap).ReturnType "int" := by
  obtain ⟨xs, found⟩ := Mutable.Value.ints_of_hasType typed
  exact .inr ⟨_, [], heap, heap.length, (consecutive_count.result xs heap address [] found).finishes, rfl⟩

theorem consecutive_count.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P93Ast.module "consecutive_count" [.ref address] heap).Supported :=
  (consecutive_count.«Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p93
