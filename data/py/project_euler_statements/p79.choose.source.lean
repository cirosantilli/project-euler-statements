import data.«project-euler-statements».data.py.project_euler_statements.«p79.edges.source»
import lang.py.FormalSW.NextCalls
import Mathlib.Data.String.Basic

/-! The reference's lazy first-ready scan agrees with the least eligible vertex of a sorted list. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def readyTest : Expr := .unaryOp .not (.call (.name "incoming") [.name "n", .name "es"])

def nextReady : Expr :=
  .consumeGenerator (nextConsumer (some (.constant .none))) (.name "n")
    [(.name "n", .name "ns", [readyTest])]

abbrev topoCode : List Stmt := executableBody
  ((findFunctionIn program.body "topo").getD ([], [])).2

theorem find_source : (match (topoCode[2]? : Option Stmt) with
    | some (Stmt.whileDo _ body _) => body[0]?
    | _ => none) = some (.assign [.name "found"] nextReady) := rfl

theorem not_incoming (entries : List Edge) (node : String) :
    (!(entries.any (fun edge => decide (edge.2.2 = node)))) =
      decide (Ready node (entries.map Prod.snd)) := by
  cases flag : entries.any (fun edge => decide (edge.2.2 = node)) with
  | false => simp [(incoming_false_iff entries node).mp flag]
  | true =>
      have notReady : ¬ Ready node (entries.map Prod.snd) := by
        intro ready
        have absent := (incoming_false_iff entries node).mpr ready
        rw [flag] at absent
        contradiction
      simp [notReady]

theorem ready_test (heap : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges heap address entries) (env : HeapCalls.Env) (node : String)
    (getNode : env "n" = some (text node)) (getEdges : env "es" = some (.ref address)) :
    Evaluates program env readyTest heap
      (.scalar (.bool (decide (Ready node (entries.map Prod.snd))))) heap := by
  have called := Evaluates.call
    (.cons (Evaluates.lookup getNode) (.cons (Evaluates.lookup getEdges) .nil))
    (incoming_result heap address entries edges node)
  have negated := Evaluates.unary (op := UnaryOp.not) called rfl
  simpa only [scalarTruth, not_incoming] using negated

theorem next_ready_result (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (env : HeapCalls.Env)
    (getNodes : env "ns" = some (.ref nodesAddress))
    (getEdges : env "es" = some (.ref edgesAddress)) :
    Evaluates program env nextReady heap
      (((nodes.find? (fun node => decide (Ready node (entries.map Prod.snd)))).map text).getD
        (.scalar .none)) heap := by
  let invariant := fun inner : HeapCalls.Env =>
    inner "es" = some (.ref edgesAddress) ∧ inner nextDefault = some (.scalar .none)
  apply Evaluates.next_generator_sequence (fallback := some (.constant .none))
    (by intros; intro impossible; cases impossible)
    (by intros; intro impossible; cases impossible)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getNodes)
    (nextSequence_list heap nodesAddress _ found) Evaluates.constant
  apply find_sequence_loop nodes text (fun node => decide (Ready node (entries.map Prod.snd)))
    readyTest (.name "n") (.name nextDefault) "n" (.ref nodesAddress) heap (.scalar .none)
    invariant
  · intro inner item valid
    simpa [invariant, setLocal, nextDefault] using valid
  · intro inner item valid lookup
    exact ready_test heap edgesAddress entries edges inner item lookup valid.1
  · intro inner item _ lookup
    exact Evaluates.lookup lookup
  · intro inner valid
    exact Evaluates.lookup valid.2
  · simp [sequenceValue, Mutable.sequence, found]
  · constructor
    · simpa [nextEnv, setLocal, nextDefault, comprehensionTargetsEnv, targetLocals] using getEdges
    · simp [nextEnv, setLocal]
  · rfl

theorem sorted_find_choose (nodes : List String) (edges : List (String × String))
    (sorted : nodes.Pairwise (· ≤ ·)) :
    nodes.find? (fun node => decide (Ready node edges)) = choose nodes edges := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      have sortedRest := List.pairwise_cons.mp sorted
      by_cases ready : Ready node edges
      · have minimum : choose (node :: rest) edges = some node := by
          apply List.min?_eq_some_iff.mpr
          constructor
          · simp [ready]
          · intro other member
            have present := (List.mem_filter.mp member).1
            rcases List.mem_cons.mp present with same | tail
            · subst other; exact le_rfl
            · exact sortedRest.1 other tail
        simp [ready, minimum]
      · simpa [choose, ready] using ih sortedRest.2

/-- The actual reference expression selects the same greedy vertex used by the optimized proof. -/
theorem next_ready_choose (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (sorted : nodes.Pairwise (· ≤ ·))
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref nodesAddress))
    (getEdges : env "es" = some (.ref edgesAddress)) :
    Evaluates program env nextReady heap
      (((choose nodes (entries.map Prod.snd)).map text).getD (.scalar .none)) heap := by
  simpa only [sorted_find_choose nodes _ sorted] using
    next_ready_result heap nodesAddress edgesAddress nodes entries found edges env getNodes getEdges

end data.«project-euler-statements».data.py.project_euler_statements.p79
