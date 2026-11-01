import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».RotationCore
import lang.py.FormalSW.HeapMemoCallRules

/-! The compiler's rotation-label tuple may already be cached by an earlier helper call. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.expand69
open FormalSW.PyAst ProjectEulerSolutions
set_option Elab.async false

namespace pool

def expression : Expr :=
  match (code[1]? : Option Stmt) with
  | some (.ifThen _ [.forIn _ iterable _ _] _) => iterable
  | _ => .constant .none

def identity : String := (HeapMemoCalls.pooledIdentity expression).getD ""
def key : HeapMemoCalls.Key := HeapMemoCalls.literalKey identity

theorem expression_eq : expression = HeapMemoCalls.pooledTuple identity
    [.constant (.int 6), .constant (.int 9)] := rfl

def Found (heap : Mutable.Heap) (value : Mutable.Value) : Prop :=
  ∃ address, value = .ref address ∧ heap[address]? = some (.tuple [number 6, number 9])

def spec (heap : Mutable.Heap) (query : HeapMemoCalls.Key) (value : Mutable.Value) : Prop :=
  query = key ∧ Found heap value

theorem preserves_append (heap extra : Mutable.Heap) :
    HeapMemoCalls.Cache.Preserves spec heap (heap ++ extra) := by
  intro cache valid query value cached
  obtain ⟨same, address, rfl, found⟩ := valid query value cached
  exact ⟨same, address, rfl, HeapCollection.prefix_found heap extra address _ found⟩

/-- Appending rotation labels affects only the fresh output list, never a cached tuple. -/
theorem preserves_output (base : Mutable.Heap) (labels replacement : List Nat) (garbage : Mutable.Heap) :
    HeapMemoCalls.Cache.Preserves spec (working base labels garbage) (working base replacement garbage) := by
  intro cache valid query value cached
  obtain ⟨same, address, rfl, found⟩ := valid query value cached
  exact ⟨same, address, rfl, tuple_preserved base labels replacement garbage address _ found⟩

def Post (heap : Mutable.Heap) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∃ extra, after = heap ++ extra ∧ Found after value

/-- Both cache outcomes produce the real tuple and preserve every existing object. -/
theorem evaluate (env : HeapCalls.Env) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapMemoCalls.EvaluatesRel program spec env expression heap (Post heap) globals := by
  rw [expression_eq]
  apply HeapMemoCalls.EvaluatesRel.pooled_tuple
  · have allocated := HeapMemoCalls.Evaluates.tuple (module := program) (spec := spec)
      (env := env) (heap := heap) (globals := globals)
      (.cons (HeapMemoCalls.Evaluates.constant (value := .int 6))
        (.cons (HeapMemoCalls.Evaluates.constant (value := .int 9)) .nil))
      (preserves_append heap [.tuple [number 6, number 9]]) (by simp)
    apply allocated.rel.consequence
    rintro value after ⟨rfl, rfl⟩
    have found : Found (heap ++ [.tuple [number 6, number 9]]) (.ref heap.length) :=
      ⟨heap.length, rfl, by simp⟩
    exact ⟨⟨[.tuple [number 6, number 9]], rfl, found⟩, rfl, found⟩
  · intro value cached
    exact ⟨[], by simp, cached.2⟩

end pool
end data.«project-euler-statements».data.py.project_euler_statements.p90.expand69
