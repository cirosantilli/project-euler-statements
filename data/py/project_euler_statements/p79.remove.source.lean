import data.«project-euler-statements».data.py.project_euler_statements.«p79.filter.source»
import Mathlib.Data.String.Basic

/-! The reference removes incident edges without changing the surviving tuple objects. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def retain (node : String) (edge : Edge) : Bool :=
  decide (edge.2.1 ≠ node ∧ edge.2.2 ≠ node)

def removeTest : Expr := .boolOp .and
  [.compare (.subscript (.name "e") (.constant (.int 0))) [(.notEq, .name "n")],
   .compare (.subscript (.name "e") (.constant (.int 1))) [(.notEq, .name "n")]]

def removeExpr : Expr := .listComp (.name "e") [("e", .name "es", [removeTest])]

theorem remove_source : executableBody
    ((findFunctionIn program.body "remove_node").getD ([], [])).2 = [.return removeExpr] := rfl

theorem remove_test (heap : Mutable.Heap) (edge : Edge) (stored : Stored heap edge)
    (node : String) (env : HeapCalls.Env) (getNode : env "n" = some (text node))
    (getEdge : env "e" = some (edgeValue edge)) :
    Evaluates program env removeTest heap (.scalar (.bool (retain node edge))) heap := by
  have first : Evaluates program env
      (.compare (.subscript (.name "e") (.constant (.int 0))) [(.notEq, .name "n")])
      heap (.scalar (.bool (decide (edge.2.1 ≠ node)))) heap := by
    apply Evaluates.compare (edge_first heap edge stored env getEdge) (Evaluates.lookup getNode)
    simp [HeapCalls.compare, scalarCompare]
  by_cases different : edge.2.1 ≠ node
  · have flag : decide (edge.2.1 ≠ node) = true := by simp [different]
    rw [flag] at first
    have second : Evaluates program env
        (.compare (.subscript (.name "e") (.constant (.int 1))) [(.notEq, .name "n")])
        heap (.scalar (.bool (decide (edge.2.2 ≠ node)))) heap := by
      apply Evaluates.compare (edge_second heap edge stored env getEdge) (Evaluates.lookup getNode)
      simp [HeapCalls.compare, scalarCompare]
    have combined := Evaluates.boolean_next (op := BoolOp.and) (value := .scalar (.bool true))
      first rfl rfl
      (Evaluates.boolean_last second rfl)
    simpa [retain, different] using combined
  · have flag : decide (edge.2.1 ≠ node) = false := by simp [different]
    rw [flag] at first
    have combined := Evaluates.boolean_stop (op := BoolOp.and) (value := .scalar (.bool false))
      (rest := [.compare (.subscript (.name "e") (.constant (.int 1))) [(.notEq, .name "n")]])
      first rfl rfl
    simpa [retain, different] using combined

theorem remove_result (base : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges base address entries) (node : String) :
    ReturnsValue program "remove_node" [text node, .ref address] base (.ref base.length)
      (base ++ [.list ((entries.filter (retain node)).map edgeValue)]) := by
  let args := ((findFunctionIn program.body "remove_node").getD ([], [])).1
  let body := ((findFunctionIn program.body "remove_node").getD ([], [])).2
  let env := functionEnv args body [text node, .ref address] []
  let inner := comprehensionEnv env [("e", .name "es", [removeTest])]
  let invariant := fun current : HeapCalls.Env => current "n" = some (text node)
  have valid : invariant inner := rfl
  obtain ⟨finalEnv, filtered, _⟩ := filter_loop base address entries edgeValue (retain node)
    removeTest "e" edges.found invariant
    (by intro current item bound; simpa [invariant, setLocal] using bound)
    (by
      intro current item collected bound member lookup
      exact remove_test _ item ((edges.stored item member).append base _ item)
        node current bound lookup) [] entries [] rfl inner valid
  apply BlockReturns.function (args := args) (body := body) rfl rfl
  change BlockReturns program env [.return removeExpr] base _ _
  apply BlockReturns.return_value
  apply Evaluates.list_comp_sequence (items := entries.map edgeValue)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup rfl)
    (by simp [Mutable.sequence, edges.found])
  simpa only [List.length_nil, List.nil_append] using filtered

theorem remove_represents (base : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges base address entries) (node : String) :
    Edges (base ++ [.list ((entries.filter (retain node)).map edgeValue)]) base.length
      (entries.filter (retain node)) := by
  constructor
  · simp
  · intro edge member
    exact (edges.stored edge (List.mem_filter.mp member).1).append base _ edge

theorem remove_contents (entries : List Edge) (node : String) :
    (entries.filter (retain node)).map Prod.snd = removeNode node (entries.map Prod.snd) := by
  induction entries with
  | nil => rfl
  | cons edge rest ih =>
      by_cases keep : edge.2.1 ≠ node ∧ edge.2.2 ≠ node <;>
        simp_all [retain, removeNode]

end data.«project-euler-statements».data.py.project_euler_statements.p79
