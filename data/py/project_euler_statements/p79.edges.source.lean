import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p79.py.ast»
import lang.py.FormalSW.TruthCalls
import ProjectEulerStatements.Lib.TopologicalOrder

/-! Reference edge scans read shared tuple objects and stop at the first incoming constraint. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

abbrev program := P79Ast.module
abbrev text (value : String) : Mutable.Value := .scalar (.string value)
abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
abbrev Edge := Nat × (String × String)
abbrev edgeValue (edge : Edge) : Mutable.Value := .ref edge.1

def Stored (heap : Mutable.Heap) (edge : Edge) : Prop :=
  heap[edge.1]? = some (.tuple [text edge.2.1, text edge.2.2])

structure Edges (heap : Mutable.Heap) (address : Nat) (entries : List Edge) : Prop where
  found : heap[address]? = some (.list (entries.map edgeValue))
  stored : ∀ edge ∈ entries, Stored heap edge

theorem Stored.append (heap extra : Mutable.Heap) (edge : Edge) (stored : Stored heap edge) :
    Stored (heap ++ extra) edge := by
  rw [Stored, List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]
  exact stored

theorem Edges.append (heap extra : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges heap address entries) : Edges (heap ++ extra) address entries := by
  constructor
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp edges.found).1]
    exact edges.found
  · exact fun edge member => (edges.stored edge member).append heap extra edge

theorem edge_first (heap : Mutable.Heap) (edge : Edge) (stored : Stored heap edge)
    (env : HeapCalls.Env) (lookup : env "e" = some (edgeValue edge)) :
    Evaluates program env (.subscript (.name "e") (.constant (.int 0)))
      heap (text edge.2.1) heap := by
  apply Evaluates.subscript (by intros; intro impossible; cases impossible)
    (Evaluates.lookup lookup) Evaluates.constant
  change heap[edge.1]? = _ at stored
  simp [Mutable.getItem, stored, Mutable.index, Except.map]

theorem edge_second (heap : Mutable.Heap) (edge : Edge) (stored : Stored heap edge)
    (env : HeapCalls.Env) (lookup : env "e" = some (edgeValue edge)) :
    Evaluates program env (.subscript (.name "e") (.constant (.int 1)))
      heap (text edge.2.2) heap := by
  apply Evaluates.subscript (by intros; intro impossible; cases impossible)
    (Evaluates.lookup lookup) Evaluates.constant
  change heap[edge.1]? = _ at stored
  simp [Mutable.getItem, stored, Mutable.index, Except.map]

def incomingTest : Expr :=
  .compare (.subscript (.name "e") (.constant (.int 1))) [(.eq, .name "n")]

def incomingExpr : Expr :=
  .consumeGenerator (.builtinCall .any []) incomingTest [(.name "e", .name "es", [])]

theorem incoming_source : executableBody
    ((findFunctionIn program.body "incoming").getD ([], [])).2 = [.return incomingExpr] := rfl

theorem incoming_loop (heap : Mutable.Heap) (address : Nat) (entries before remaining : List Edge)
    (edges : Edges heap address entries) (partition : entries = before ++ remaining)
    (node : String) (env : HeapCalls.Env) (getNode : env "n" = some (text node)) :
    BlockReturns program env
      [.sequenceStepLoop "e" (.ref address) before.length (truthBody false incomingTest) [],
       .return (.constant (.bool false))]
      heap (.scalar (.bool (remaining.any (fun edge => decide (edge.2.2 = node))))) heap := by
  induction remaining generalizing before env with
  | nil =>
      apply BlockReturns.sequence_done (items := entries.map edgeValue)
        (by simp [sequenceValue, Mutable.sequence, edges.found])
      · simp [partition]
      · exact BlockReturns.return_value Evaluates.constant
  | cons edge rest ih =>
      have stored := edges.stored edge (by simp [partition])
      have tested : Evaluates program (setLocal env "e" (edgeValue edge)) incomingTest heap
          (.scalar (.bool (decide (edge.2.2 = node)))) heap := by
        apply Evaluates.compare (edge_second heap edge stored _ (by simp [setLocal]))
          (Evaluates.lookup (by simpa [setLocal] using getNode))
        simp [HeapCalls.compare, scalarCompare]
      apply BlockReturns.sequence_step (value := edgeValue edge) (items := entries.map edgeValue)
        (by simp [sequenceValue, Mutable.sequence, edges.found])
        (by simp [partition])
      by_cases incoming : edge.2.2 = node
      · simp only [List.any_cons, incoming, decide_true, Bool.true_or]
        apply BlockReturns.branch (flag := true) (by simpa [incoming] using tested) rfl
        exact BlockReturns.return_value Evaluates.constant
      · simp only [List.any_cons, incoming, decide_false, Bool.false_or]
        apply BlockReturns.branch (flag := false) (by simpa [incoming] using tested) rfl
        have continued := ih (before ++ [edge]) (by simpa [List.append_assoc] using partition)
          (setLocal env "e" (edgeValue edge)) (by simpa [setLocal] using getNode)
        simpa [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt]
          using continued

theorem incoming_result (heap : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges heap address entries) (node : String) :
    ReturnsValue program "incoming" [text node, .ref address] heap
      (.scalar (.bool (entries.any (fun edge => decide (edge.2.2 = node))))) heap := by
  apply BlockReturns.function rfl rfl
  change BlockReturns program _ [.return incomingExpr] heap _ heap
  apply BlockReturns.return_value
  apply Evaluates.truth_generator_sequence (universal := false) (items := entries.map edgeValue)
    (by intros; intro impossible; cases impossible)
    (by intros; intro impossible; cases impossible)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup rfl)
    (by simp [Mutable.sequence, edges.found])
  exact incoming_loop heap address entries [] entries edges rfl node _ (by
    simp [comprehensionTargetsEnv, targetLocals, functionEnv, HeapCalls.argumentEnv])

theorem incoming_false_iff (entries : List Edge) (node : String) :
    entries.any (fun edge => decide (edge.2.2 = node)) = false ↔
      Ready node (entries.map Prod.snd) := by
  simp [Ready]
  constructor
  · intro absent source target address member
    exact absent address source target member
  · intro absent address source target member
    exact absent source target address member

end data.«project-euler-statements».data.py.project_euler_statements.p79
