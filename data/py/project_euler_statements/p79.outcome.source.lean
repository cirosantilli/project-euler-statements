import data.«project-euler-statements».data.py.project_euler_statements.«p79.edges.source»

/-! Source results resume the caller on success and propagate exceptions on failure. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def SourceResult (work : Work) (heap : Mutable.Heap)
    (outcome : Except ExceptionObject Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∀ anchors stack, match outcome with
    | .ok value => Reaches program anchors ⟨work, stack, heap⟩ ⟨.value value, stack, after⟩
    | .error error => Finishes (HeapCalls.step program anchors) ⟨work, stack, heap⟩
        (.ok ⟨.error error, [], after, anchors⟩)

theorem SourceResult.before (work next : Work) (heap middle after : Mutable.Heap)
    (outcome : Except ExceptionObject Mutable.Value)
    (reach : ∀ anchors stack, Reaches program anchors ⟨work, stack, heap⟩ ⟨next, stack, middle⟩)
    (result : SourceResult next middle outcome after) : SourceResult work heap outcome after := by
  intro anchors stack
  cases outcome with
  | ok value => exact (reach anchors stack).trans (result anchors stack)
  | error error => exact (reach anchors stack).finishes (result anchors stack)

theorem SourceResult.finishes (work : Work) (heap after : Mutable.Heap)
    (outcome : Except ExceptionObject Mutable.Value) (result : SourceResult work heap outcome after)
    (anchors : Nat) :
    Finishes (HeapCalls.step program anchors) ⟨work, [], heap⟩
      (.ok ⟨outcome, [], after, anchors⟩) := by
  cases outcome with
  | ok value => exact (result anchors []).finishes (.done rfl)
  | error error => exact result anchors []

theorem source_call (env : HeapCalls.Env) (name : String) (expressions : List Expr)
    (heap middle after : Mutable.Heap) (values : List Mutable.Value)
    (outcome : Except ExceptionObject Mutable.Value)
    (arguments : Evaluates.Arguments program env expressions heap values middle)
    (result : SourceResult (.operation (.call name) values) middle outcome after) :
    SourceResult (.expr (.call (.name name) expressions) env) heap outcome after := by
  apply SourceResult.before _ _ heap middle after outcome _ result
  intro anchors stack
  exact .next rfl (Evaluates.arguments_reach arguments (.call name) [] anchors stack)

end data.«project-euler-statements».data.py.project_euler_statements.p79
