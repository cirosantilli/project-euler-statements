import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p79.py.ast»
import lang.py.FormalSW.TruthCalls
import ProjectEulerStatements.Lib.TopologicalOrder
import ProjectEulerStatements.Lib.PrecedenceTriples
import lang.py.FormalSW.NextCalls
import Mathlib.Data.String.Basic
import ProjectEulerStatements.Lib.StringSorting
import lang.py.FormalSW.DigitCalls
import lang.py.FormalSW.ReprCalls
import lang.py.FormalSW.SetChoiceCalls
import lang.py.FormalSW.IteratorRules
import lang.py.FormalSW.ConstructionIsolation
import lang.py.FormalSW.IteratorOperationRelocation
import lang.py.FormalSW.IteratorExecutionIsolation
import lang.py.FormalSW.IteratorPrefix
import lang.py.FormalSW.IteratorAcquisitionIsolation

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

/-! Reference duplicate removal compares contents, including separately allocated edge tuples. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

theorem sequence_contains_by {α β : Type} [DecidableEq β] (heap : Mutable.Heap)
    (encode : α → Mutable.Value) (key : α → β) (items : List α) (needle : α)
    (identity : ∀ item ∈ items, encode item = encode needle → key item = key needle)
    (compared : ∀ item ∈ items, HeapCalls.compare .eq (encode item) (encode needle) heap =
      some (.ok (.scalar (.bool (decide (key item = key needle)))), heap)) :
    sequenceContains (encode needle) (items.map encode) heap =
      some (.ok (decide (key needle ∈ items.map key)), heap) := by
  induction items with
  | nil => simp [sequenceContains]
  | cons item rest ih =>
      have restResult := ih (fun other member => identity other (by simp [member]))
        (fun other member => compared other (by simp [member]))
      by_cases sameValue : encode item = encode needle
      · have sameKey := identity item (by simp) sameValue
        simp [sequenceContains, sameValue, sameKey]
      · have tested := compared item (by simp)
        by_cases sameKey : key item = key needle
        · simp [sequenceContains, sameValue, tested, sameKey, Mutable.truth, scalarTruth]
        · simp [sequenceContains, sameValue, tested, sameKey, Ne.symm sameKey,
            Mutable.truth, scalarTruth, restResult]

theorem list_membership_by {α β : Type} [DecidableEq β] (heap : Mutable.Heap) (address : Nat)
    (encode : α → Mutable.Value) (key : α → β) (items : List α) (needle : α)
    (found : heap[address]? = some (.list (items.map encode)))
    (identity : ∀ item ∈ items, encode item = encode needle → key item = key needle)
    (compared : ∀ item ∈ items, HeapCalls.compare .eq (encode item) (encode needle) heap =
      some (.ok (.scalar (.bool (decide (key item = key needle)))), heap)) :
    membership (encode needle) (.ref address) true heap =
      some (.ok (.scalar (.bool (decide (key needle ∉ items.map key)))), heap) := by
  simp [membership, found, sequence_contains_by heap encode key items needle identity compared,
    Except.map, -List.mem_map]

theorem strings_membership (heap : Mutable.Heap) (address : Nat) (items : List String)
    (needle : String) (found : heap[address]? = some (.list (items.map text))) :
    membership (text needle) (.ref address) true heap =
      some (.ok (.scalar (.bool (decide (needle ∉ items)))), heap) := by
  simpa using list_membership_by heap address text id items needle found
    (by intro item _ same; simpa using same)
    (by intro item _; simp [HeapCalls.compare, scalarCompare])

theorem edge_identity (heap : Mutable.Heap) (left right : Edge)
    (storedLeft : Stored heap left) (storedRight : Stored heap right)
    (same : edgeValue left = edgeValue right) : left.2 = right.2 := by
  have addresses : left.1 = right.1 := by simpa using same
  change heap[left.1]? = _ at storedLeft
  change heap[right.1]? = _ at storedRight
  rw [addresses, storedRight] at storedLeft
  simp only [Option.some.injEq, Mutable.Object.tuple.injEq, List.cons.injEq,
    Mutable.Value.scalar.injEq, Constant.string.injEq, and_true] at storedLeft
  exact Prod.ext storedLeft.1.symm storedLeft.2.symm

theorem edge_compare (heap : Mutable.Heap) (left right : Edge)
    (storedLeft : Stored heap left) (storedRight : Stored heap right) :
    HeapCalls.compare .eq (edgeValue left) (edgeValue right) heap =
      some (.ok (.scalar (.bool (decide (left.2 = right.2)))), heap) := by
  have leftFound := storedLeft
  have rightFound := storedRight
  change heap[left.1]? = _ at leftFound
  change heap[right.1]? = _ at rightFound
  by_cases sameAddress : left.1 = right.1
  · have same := edge_identity heap left right storedLeft storedRight (by simp [sameAddress])
    simp [HeapCalls.compare, rightFound, sameAddress, same]
    rfl
  · by_cases first : left.2.1 = right.2.1 <;>
      by_cases second : left.2.2 = right.2.2 <;>
        simp [HeapCalls.compare, leftFound, rightFound, sameAddress, equalLists, equalElements,
          scalarCompare, first, second, Prod.ext_iff] <;> rfl

theorem edges_membership (heap : Mutable.Heap) (address : Nat) (entries : List Edge)
    (needle : Edge) (found : heap[address]? = some (.list (entries.map edgeValue)))
    (stored : ∀ entry ∈ entries, Stored heap entry) (needleStored : Stored heap needle) :
    membership (edgeValue needle) (.ref address) true heap =
      some (.ok (.scalar (.bool (decide (needle.2 ∉ entries.map Prod.snd)))), heap) := by
  simpa using list_membership_by heap address edgeValue Prod.snd entries needle found
    (fun entry member => edge_identity heap entry needle (stored entry member) needleStored)
    (fun entry member => edge_compare heap entry needle (stored entry member) needleStored)

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The source keeps the first representative of each content key, without copying its elements. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def dedupBy {α β : Type} [DecidableEq β] (key : α → β) (collected : List α) : List α → List α
  | [] => collected
  | item :: rest =>
      dedupBy key (if key item ∈ collected.map key then collected else collected ++ [item]) rest

theorem dedupBy_subset {α β : Type} [DecidableEq β] (key : α → β)
    (collected remaining : List α) : dedupBy key collected remaining ⊆ collected ++ remaining := by
  induction remaining generalizing collected with
  | nil => simp [dedupBy]
  | cons item rest ih =>
      unfold dedupBy
      split
      · apply (ih collected).trans
        intro x member
        rcases List.mem_append.mp member with before | after
        · exact List.mem_append_left _ before
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
      · exact (ih (collected ++ [item])).trans
          (by intro x member; simpa only [List.append_assoc, List.singleton_append] using member)

theorem dedupBy_keys {α β : Type} [DecidableEq β] (key : α → β)
    (collected remaining : List α) (value : β) :
    value ∈ (dedupBy key collected remaining).map key ↔
      value ∈ collected.map key ∨ value ∈ remaining.map key := by
  induction remaining generalizing collected with
  | nil => simp [dedupBy]
  | cons item rest ih =>
      by_cases present : key item ∈ collected.map key
      · simp only [dedupBy, if_pos present, ih, List.map_cons, List.mem_cons]
        constructor
        · exact fun member => member.elim Or.inl (fun tail => Or.inr (Or.inr tail))
        · rintro (member | same | tail)
          · exact Or.inl member
          · exact Or.inl (same ▸ present)
          · exact Or.inr tail
      · simp [dedupBy, present, ih, or_assoc]

theorem dedupBy_unique {α β : Type} [DecidableEq β] (key : α → β)
    (collected remaining : List α) (unique : (collected.map key).Nodup) :
    ((dedupBy key collected remaining).map key).Nodup := by
  induction remaining generalizing collected with
  | nil => exact unique
  | cons item rest ih =>
      unfold dedupBy
      split_ifs with present
      · exact ih collected unique
      · apply ih
        simp [List.map_append, List.nodup_append, unique, -List.mem_map]
        intro value member same
        exact present (same ▸ member)

def dedupBody : List Stmt :=
  [.ifThen (.membership (.name "x") (.name "out") true)
    [.expr (.call (.attribute (.name "out") "append") [.name "x"])] []]

theorem dedup_source : executableBody
    ((findFunctionIn program.body "erase_dups").getD ([], [])).2 =
      [.assign [.name "out"] (.list []),
       .forIn (.name "x") (.name "xs") dedupBody [], .return (.name "out")] := rfl

theorem dedup_loop {α β : Type} [DecidableEq β] (base : Mutable.Heap) (address : Nat)
    (items : List α) (encode : α → Mutable.Value) (key : α → β)
    (found : base[address]? = some (.list (items.map encode)))
    (tested : ∀ item ∈ items, ∀ collected : List α, collected ⊆ items →
      membership (encode item) (.ref base.length) true (base ++ [.list (collected.map encode)]) =
        some (.ok (.scalar (.bool (decide (key item ∉ collected.map key)))),
          base ++ [.list (collected.map encode)]))
    (before remaining collected : List α) (partition : items = before ++ remaining)
    (subset : collected ⊆ items) (env : HeapCalls.Env)
    (getOut : env "out" = some (.ref base.length)) :
    BlockReturns program env
      [.sequenceStepLoop "x" (.ref address) before.length dedupBody [], .return (.name "out")]
      (base ++ [.list (collected.map encode)]) (.ref base.length)
      (base ++ [.list ((dedupBy key collected remaining).map encode)]) := by
  have input (values : List α) : (base ++ [.list (values.map encode)])[address]? =
      some (.list (items.map encode)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  induction remaining generalizing before collected env with
  | nil =>
      apply BlockReturns.sequence_done (items := items.map encode)
        (by simp [sequenceValue, Mutable.sequence, input])
      · simp [partition]
      · exact BlockReturns.return_value (Evaluates.lookup getOut)
  | cons item rest ih =>
      let bound := setLocal env "x" (encode item)
      have outBound : bound "out" = some (.ref base.length) := by
        simpa [bound, setLocal] using getOut
      have member : item ∈ items := by simp [partition]
      have membershipResult : Evaluates program bound
          (.membership (.name "x") (.name "out") true)
          (base ++ [.list (collected.map encode)])
          (.scalar (.bool (decide (key item ∉ collected.map key))))
          (base ++ [.list (collected.map encode)]) :=
        Evaluates.membership
          (.cons (Evaluates.lookup (by simp [bound, setLocal]))
            (.cons (Evaluates.lookup outBound) .nil)) (tested item member collected subset)
      let next := if key item ∈ collected.map key then collected else collected ++ [item]
      have nextSubset : next ⊆ items := by
        dsimp [next]
        split_ifs
        · exact subset
        · intro x present
          rcases List.mem_append.mp present with previous | added
          · exact subset previous
          · simpa using (List.mem_singleton.mp added ▸ member)
      have iteration : BlockContinues program bound dedupBody
          (base ++ [.list (collected.map encode)]) bound (base ++ [.list (next.map encode)]) := by
        by_cases present : key item ∈ collected.map key
        · simpa only [next, if_pos present] using
            (BlockContinues.branch (flag := false)
              (by simpa only [present, not_true_eq_false, decide_false] using membershipResult)
              rfl BlockContinues.nil)
        · apply BlockContinues.branch (flag := true)
            (by simpa only [present, not_false_eq_true, decide_true] using membershipResult) rfl
          apply BlockContinues.discard
          have appended := Evaluates.append (module := program) (globals := [])
            (value := encode item) (current := collected.map encode)
            (Evaluates.lookup (name := "out") outBound)
            (show (base ++ [.list (collected.map encode)])[base.length]? =
              some (.list (collected.map encode)) by simp)
            (Evaluates.lookup (name := "x") (by simp [bound, setLocal])) (by simp)
          simpa [next, present, List.map_append] using appended
      have continued := ih (before ++ [item]) next
        (by simpa [List.append_assoc] using partition) nextSubset bound outBound
      apply BlockReturns.sequence_step (items := items.map encode) (value := encode item)
        (by simp [sequenceValue, Mutable.sequence, input]) (by simp [partition])
      simpa [dedupBy, next, dedupBody, Calls.loopContinuation, Calls.loopControl,
        Calls.loopControlStmt] using iteration.returns continued

theorem dedup_result {α β : Type} [DecidableEq β] (base : Mutable.Heap) (address : Nat)
    (items : List α) (encode : α → Mutable.Value) (key : α → β)
    (found : base[address]? = some (.list (items.map encode)))
    (tested : ∀ item ∈ items, ∀ collected : List α, collected ⊆ items →
      membership (encode item) (.ref base.length) true (base ++ [.list (collected.map encode)]) =
        some (.ok (.scalar (.bool (decide (key item ∉ collected.map key)))),
          base ++ [.list (collected.map encode)])) :
    ReturnsValue program "erase_dups" [.ref address] base (.ref base.length)
      (base ++ [.list ((dedupBy key [] items).map encode)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply BlockReturns.for_sequence (items := items.map encode)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup rfl)
    (by
      simp [Mutable.sequence, List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp found).1, found])
  exact dedup_loop base address items encode key found tested [] items [] rfl (by simp) _
    (by simp [setLocal])

theorem dedup_strings (base : Mutable.Heap) (address : Nat) (items : List String)
    (found : base[address]? = some (.list (items.map text))) :
    ReturnsValue program "erase_dups" [.ref address] base (.ref base.length)
      (base ++ [.list ((dedupBy id [] items).map text)]) := by
  apply dedup_result base address items text id found
  intro item _ collected _
  simpa using strings_membership (base ++ [.list (collected.map text)]) base.length collected
    item (by simp)

theorem dedup_edges (base : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges base address entries) :
    ReturnsValue program "erase_dups" [.ref address] base (.ref base.length)
      (base ++ [.list ((dedupBy Prod.snd [] entries).map edgeValue)]) := by
  apply dedup_result base address entries edgeValue Prod.snd edges.found
  intro item member collected subset
  simpa using edges_membership (base ++ [.list (collected.map edgeValue)]) base.length collected
    item (by simp)
    (fun entry present => (edges.stored entry (subset present)).append base _ entry)
    ((edges.stored item member).append base _ item)

theorem dedup_edges_represents (base : Mutable.Heap) (address : Nat) (entries : List Edge)
    (edges : Edges base address entries) :
    Edges (base ++ [.list ((dedupBy Prod.snd [] entries).map edgeValue)]) base.length
      (dedupBy Prod.snd [] entries) := by
  constructor
  · simp
  · intro entry member
    have original := dedupBy_subset Prod.snd [] entries member
    exact (edges.stored entry original).append base _ entry

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The nested reference comprehension visits Unicode characters and builds distinct graph nodes. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def attemptCharacters (attempts : List String) : List String :=
  attempts.flatMap (fun s => s.toList.map String.singleton)

def nodeValues (attempts : List String) : List String := dedupBy id [] (attemptCharacters attempts)

def collectNodes : Expr :=
  .listComp (.name "c") [("s", .name "attempts", []), ("c", .name "s", [])]

def collectCharacters (collector : Nat) : List Stmt :=
  [.forIn (.name "c") (.name "s") [.comprehensionAppend collector (.name "c")] []]

theorem nodes_source : executableBody
    ((findFunctionIn program.body "nodes").getD ([], [])).2 =
      [.return (.call (.name "erase_dups") [collectNodes])] := rfl

theorem collect_characters_loop (base : Mutable.Heap) (s : String)
    (before remaining : List Char) (collected : List String)
    (partition : s.toList = before ++ remaining) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "c" (.scalar (.string s)) before.length
        [.comprehensionAppend base.length (.name "c")] []]
      (base ++ [.list (collected.map text)]) finalEnv
      (base ++ [.list ((collected ++ remaining.map String.singleton).map text)]) := by
  induction remaining generalizing before collected env with
  | nil =>
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done
        (items := s.toList.map (fun c => text (String.singleton c)))
        (by simp [sequenceValue, Mutable.sequence])
      · simp [partition]
      · simpa using (BlockContinues.nil (module := program) (env := env)
          (heap := base ++ [.list (collected.map text)]))
  | cons c rest ih =>
      let bound := setLocal env "c" (text (String.singleton c))
      have emitted := BlockContinues.comprehension_append (module := program) (globals := [])
        (env := bound) (expression := .name "c") (address := base.length)
        (items := collected.map text) (heap := base ++ [.list (collected.map text)])
        (Evaluates.lookup (value := text (String.singleton c)) (by simp [bound, setLocal]))
        (by simp)
      obtain ⟨finalEnv, continued⟩ := ih (before ++ [c]) (collected ++ [String.singleton c])
        (by simpa [List.append_assoc] using partition) bound
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step
        (items := s.toList.map (fun c => text (String.singleton c)))
        (value := text (String.singleton c))
        (by simp [sequenceValue, Mutable.sequence]) (by simp [partition])
      have emitted' : BlockContinues program bound
          [.comprehensionAppend base.length (.name "c")]
          (base ++ [.list (collected.map text)]) bound
          (base ++ [.list ((collected ++ [String.singleton c]).map text)]) := by
        simpa [List.map_append] using emitted
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.append_assoc, bound] using emitted'.append continued

theorem collect_nodes_loop (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.list (attempts.map text)))
    (before remaining collected : List String) (partition : attempts = before ++ remaining)
    (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "s" (.ref address) before.length (collectCharacters base.length) []]
      (base ++ [.list (collected.map text)]) finalEnv
      (base ++ [.list ((collected ++ attemptCharacters remaining).map text)]) := by
  have input (values : List String) : (base ++ [.list (values.map text)])[address]? =
      some (.list (attempts.map text)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  induction remaining generalizing before collected env with
  | nil =>
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done (items := attempts.map text)
        (by simp [sequenceValue, Mutable.sequence, input])
      · simp [partition]
      · simpa [attemptCharacters] using (BlockContinues.nil (module := program) (env := env)
          (heap := base ++ [.list (collected.map text)]))
  | cons s rest ih =>
      let bound := setLocal env "s" (text s)
      obtain ⟨innerEnv, inner⟩ := collect_characters_loop base s [] s.toList collected rfl bound
      have collectedStep : BlockContinues program bound (collectCharacters base.length)
          (base ++ [.list (collected.map text)]) innerEnv
          (base ++ [.list ((collected ++ s.toList.map String.singleton).map text)]) := by
        apply BlockContinues.for_sequence (value := text s)
          (items := s.toList.map (fun c => text (String.singleton c)))
          (by intros; intro impossible; cases impossible)
          (Evaluates.lookup (by simp [bound, setLocal]))
          (by simp [Mutable.sequence])
        exact inner
      obtain ⟨finalEnv, continued⟩ := ih (before ++ [s])
        (collected ++ s.toList.map String.singleton)
        (by simpa [List.append_assoc] using partition) innerEnv
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (items := attempts.map text) (value := text s)
        (by simp [sequenceValue, Mutable.sequence, input]) (by simp [partition])
      simpa [collectCharacters, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        attemptCharacters, List.append_assoc, bound] using collectedStep.append continued

theorem collect_nodes_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getAttempts : env "attempts" = some (.ref address)) :
    Evaluates program env collectNodes heap (.ref heap.length)
      (heap ++ [.list ((attemptCharacters attempts).map text)]) := by
  obtain ⟨finalEnv, collected⟩ := collect_nodes_loop heap address attempts found [] attempts [] rfl
    (comprehensionEnv env [("s", .name "attempts", []), ("c", .name "s", [])])
  apply Evaluates.list_comp_sequence (items := attempts.map text)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getAttempts)
    (by simp [Mutable.sequence, found])
  simpa only [List.length_nil, List.nil_append] using collected

theorem nodes_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text))) :
    ReturnsValue program "nodes" [.ref address] heap (.ref (heap.length + 1))
      (heap ++ [.list ((attemptCharacters attempts).map text),
        .list ((nodeValues attempts).map text)]) := by
  let source := (findFunctionIn program.body "nodes").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref address] []
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have called := Evaluates.call
    (.cons (collect_nodes_result heap address attempts found env rfl) .nil)
    (dedup_strings (heap ++ [.list ((attemptCharacters attempts).map text)]) heap.length
      (attemptCharacters attempts) (by simp))
  simpa [nodeValues, List.append_assoc] using called

theorem node_values_unique (attempts : List String) : (nodeValues attempts).Nodup := by
  simpa [nodeValues] using dedupBy_unique id [] (attemptCharacters attempts) (by simp)

theorem node_values_mem (attempts : List String) (value : String) :
    value ∈ nodeValues attempts ↔
      ∃ s ∈ attempts, ∃ c ∈ s.toList, String.singleton c = value := by
  simpa [nodeValues, attemptCharacters] using
    dedupBy_keys id [] (attemptCharacters attempts) value

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Appending a separate source list to a comprehension collector retains all element references. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

theorem set_same_object (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : heap.set address object = heap := by
  obtain ⟨bounded, contents⟩ := List.getElem?_eq_some_iff.mp found
  rw [← contents]
  exact List.set_getElem_self bounded

theorem collect_refs_loop (heap : Mutable.Heap) (address collector : Nat)
    (items before remaining collected : List Mutable.Value)
    (found : heap[address]? = some (.list items))
    (outputFound : heap[collector]? = some (.list collected)) (distinct : address ≠ collector)
    (partition : items = before ++ remaining) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "e" (.ref address) before.length
        [.comprehensionAppend collector (.name "e")] []]
      heap finalEnv (heap.set collector (.list (collected ++ remaining))) := by
  induction remaining generalizing heap before collected env with
  | nil =>
      refine ⟨env, ?_⟩
      simp only [List.append_nil, set_same_object heap collector _ outputFound]
      apply BlockContinues.sequence_done (items := items)
        (by simp [sequenceValue, Mutable.sequence, found])
      · simp [partition]
      · exact .nil
  | cons item rest ih =>
      let bound := setLocal env "e" item
      let updated := heap.set collector (.list (collected ++ [item]))
      have appended : BlockContinues program bound
          [.comprehensionAppend collector (.name "e")] heap bound updated :=
        BlockContinues.comprehension_append
          (Evaluates.lookup (by simp [bound, setLocal])) outputFound
      have input : updated[address]? = some (.list items) := by
        simpa [updated, Ne.symm distinct] using found
      have output : updated[collector]? = some (.list (collected ++ [item])) := by
        simp [updated, (List.getElem?_eq_some_iff.mp outputFound).1]
      obtain ⟨finalEnv, continued⟩ := ih updated (before ++ [item]) (collected ++ [item])
        input output (by simpa [List.append_assoc] using partition) bound
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (items := items) (value := item)
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [partition])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.append_assoc, updated, bound] using appended.append continued

theorem stored_after_list_write (heap : Mutable.Heap) (address : Nat)
    (old values : List Mutable.Value) (found : heap[address]? = some (.list old))
    (entry : Edge) (stored : Stored heap entry) :
    Stored (heap.set address (.list values)) entry := by
  have different : address ≠ entry.1 := by
    intro same
    change heap[entry.1]? = _ at stored
    rw [← same, found] at stored
    cases stored
  simpa [Stored, different] using stored

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Each reference observation allocates its three precedence pairs from Unicode characters. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev character (value : Char) : String := String.ofList [value]

def characterExpr (index : Int) : Expr := .subscript (.name "s") (.constant (.int index))

def observationExpr : Expr := .ifExp
  (.compare (.builtinCall .len [.name "s"]) [(.gtE, .constant (.int 3))])
  (.list [.tuple [characterExpr 0, characterExpr 1],
    .tuple [characterExpr 1, characterExpr 2], .tuple [characterExpr 0, characterExpr 2]])
  (.list [])

def observationEnv (s : String) : HeapCalls.Env :=
  functionEnv [{ name := "s", annotation := some (.name "str") }]
    [.return observationExpr] [text s] []

def observationEntries (address : Nat) (a b c : Char) : List Edge :=
  [(address, character a, character b), (address + 1, character b, character c),
    (address + 2, character a, character c)]

def observationHeap (heap : Mutable.Heap) (a b c : Char) : Mutable.Heap := heap ++
  [.tuple [text (character a), text (character b)],
   .tuple [text (character b), text (character c)],
   .tuple [text (character a), text (character c)],
   .list ((observationEntries heap.length a b c).map edgeValue)]

theorem observation_source : executableBody
    ((findFunctionIn program.body "edges_from").getD ([], [])).2 =
      [.return observationExpr] := rfl

theorem character_read (heap : Mutable.Heap) (env : HeapCalls.Env) (s : String)
    (getS : env "s" = some (text s)) (index : Int) (value : Char)
    (found : FormalSW.Py.Builtin.Sequence.get? s.toList index = some value) :
    Evaluates program env (characterExpr index) heap (text (character value)) heap := by
  apply Evaluates.subscript (by intros; intro impossible; cases impossible)
    (Evaluates.lookup getS) Evaluates.constant
  simp [Mutable.getItem, text, Strings.get, scalarNumber, found, character]

/-- Only the first three characters are used, even when the input has a longer suffix. -/
theorem observation_result (heap : Mutable.Heap) (s : String) (a b c : Char) (tail : List Char)
    (characters : s.toList = a :: b :: c :: tail) :
    ReturnsValue program "edges_from" [text s] heap (.ref (heap.length + 3))
      (observationHeap heap a b c) := by
  apply BlockReturns.function rfl rfl
  change BlockReturns program _ [.return observationExpr] heap _ _
  apply BlockReturns.return_value
  have length : 3 ≤ s.length := by
    have sized := congrArg List.length characters
    simp only [String.length_toList, List.length_cons] at sized
    omega
  have tested : Evaluates program (observationEnv s)
      (.compare (.builtinCall .len [.name "s"]) [(.gtE, .constant (.int 3))])
      heap (.scalar (.bool true)) heap := by
    apply Evaluates.compare (av := number s.length) (bv := number 3)
      (Evaluates.builtin (finalHeap := heap) (values := [text s])
        (.cons (Evaluates.lookup rfl) .nil)
        (by simp [primitive, Mutable.length, text])) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    omega
  apply Evaluates.conditional tested rfl
  have read (base : Mutable.Heap) (index : Int) (value : Char)
      (found : FormalSW.Py.Builtin.Sequence.get? (a :: b :: c :: tail) index = some value) :=
    character_read base (observationEnv s) s rfl index value
      (by simpa only [characters] using found)
  have first := Evaluates.tuple
    (.cons (read heap 0 a rfl) (.cons (read heap 1 b rfl) .nil)) (by simp)
  let afterFirst := heap ++ [.tuple [text (character a), text (character b)]]
  let afterSecond := afterFirst ++ [.tuple [text (character b), text (character c)]]
  have second := Evaluates.tuple
    (.cons (read afterFirst 1 b rfl) (.cons (read afterFirst 2 c rfl) .nil)) (by simp)
  have third := Evaluates.tuple
    (.cons (read afterSecond 0 a rfl) (.cons (read afterSecond 2 c rfl) .nil)) (by simp)
  simpa [observationHeap, observationEntries, List.append_assoc, afterFirst, afterSecond,
    scalarTruth, Nat.add_assoc] using
    Evaluates.list (.cons first (.cons second (.cons third .nil)))

theorem observation_represents (heap : Mutable.Heap) (a b c : Char) :
    Edges (observationHeap heap a b c) (heap.length + 3)
      (observationEntries heap.length a b c) := by
  constructor
  · simp [observationHeap]
  · intro edge member
    simp only [observationEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [Stored, observationHeap]

theorem observation_contents (address : Nat) (a b c : Char) :
    (observationEntries address a b c).map Prod.snd =
      ProjectEulerStatements.TopologicalOrder.expandedEdges
        [(character a, character b, character c)] := rfl

theorem observation_short (heap : Mutable.Heap) (s : String) (short : s.length < 3) :
    ReturnsValue program "edges_from" [text s] heap (.ref heap.length)
      (heap ++ [.list []]) := by
  apply BlockReturns.function rfl rfl
  change BlockReturns program _ [.return observationExpr] heap _ _
  apply BlockReturns.return_value
  have tested : Evaluates program (observationEnv s)
      (.compare (.builtinCall .len [.name "s"]) [(.gtE, .constant (.int 3))])
      heap (.scalar (.bool false)) heap := by
    apply Evaluates.compare (av := number s.length) (bv := number 3)
      (Evaluates.builtin (finalHeap := heap) (values := [text s])
        (.cons (Evaluates.lookup rfl) .nil)
        (by simp [primitive, Mutable.length, text])) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    omega
  exact Evaluates.conditional tested rfl (Evaluates.list .nil)

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Each edge iteration allocates its pairs and appends their references to the collector. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def observationPairs (s : String) : List (String × String) := match s.toList with
  | a :: b :: c :: _ => [(character a, character b), (character b, character c),
      (character a, character c)]
  | _ => []

theorem observation_any (heap : Mutable.Heap) (s : String) :
    ∃ extra entries address,
      ReturnsValue program "edges_from" [text s] heap (.ref address) (heap ++ extra) ∧
      Edges (heap ++ extra) address entries ∧ entries.map Prod.snd = observationPairs s ∧
      heap.length ≤ address := by
  have small (short : s.length < 3) (empty : observationPairs s = []) :
      ∃ extra entries address,
        ReturnsValue program "edges_from" [text s] heap (.ref address) (heap ++ extra) ∧
        Edges (heap ++ extra) address entries ∧ entries.map Prod.snd = observationPairs s ∧
        heap.length ≤ address := by
    refine ⟨[.list []], [], heap.length, observation_short heap s short, ?_, ?_, le_rfl⟩
    · exact ⟨by simp, by simp⟩
    · simpa using empty.symm
  have size : s.toList.length = s.length := by simp
  rcases chars : s.toList with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  · exact small (by simp [chars] at size; omega) (by simp [observationPairs, chars])
  · exact small (by simp [chars] at size; omega) (by simp [observationPairs, chars])
  · exact small (by simp [chars] at size; omega) (by simp [observationPairs, chars])
  · refine ⟨_, observationEntries heap.length a b c, heap.length + 3,
      observation_result heap s a b c tail chars, observation_represents heap a b c, ?_, by omega⟩
    simp [observationEntries, observationPairs, chars]

def collectEdgeBody (collector : Nat) : List Stmt :=
  [.forIn (.name "e") (.call (.name "edges_from") [.name "s"])
    [.comprehensionAppend collector (.name "e")] []]

theorem collect_edge_step (heap : Mutable.Heap) (collector : Nat) (collected : List Edge)
    (edges : Edges heap collector collected) (env : HeapCalls.Env) (s : String)
    (getS : env "s" = some (text s)) :
    ∃ after entries finalEnv,
      BlockContinues program env (collectEdgeBody collector) heap finalEnv after ∧
      Edges after collector entries ∧ entries.map Prod.snd = collected.map Prod.snd ++
        observationPairs s ∧ heap.length ≤ after.length ∧
      (∀ address < heap.length, address ≠ collector → after[address]? = heap[address]?) := by
  obtain ⟨extra, added, address, executed, represented, pairs, fresh⟩ := observation_any heap s
  have bounded := (List.getElem?_eq_some_iff.mp edges.found).1
  have separate : address ≠ collector := by omega
  have extended := edges.append heap extra collector collected
  obtain ⟨finalEnv, copied⟩ := collect_refs_loop (heap ++ extra) address collector
    (added.map edgeValue) [] (added.map edgeValue) (collected.map edgeValue)
    represented.found extended.found separate rfl env
  let after := (heap ++ extra).set collector (.list ((collected ++ added).map edgeValue))
  refine ⟨after, collected ++ added, finalEnv, ?_, ?_, ?_, ?_, ?_⟩
  · apply BlockContinues.for_sequence (items := added.map edgeValue)
      (by intro expressions; simp)
      (Evaluates.call (.cons (Evaluates.lookup getS) .nil) executed)
      (by simp [Mutable.sequence, represented.found])
    simpa [after, List.map_append] using copied
  · constructor
    · exact List.getElem?_set_self (by simp; omega)
    · intro entry member
      apply stored_after_list_write (heap ++ extra) collector (collected.map edgeValue)
        _ extended.found entry
      rcases List.mem_append.mp member with old | new
      · exact extended.stored entry old
      · exact represented.stored entry new
  · simp [pairs]
  · simp [after]
  · intro index inside different
    simp [after, Ne.symm different, List.getElem?_append_left, inside]

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The reference edge builder collects all observations and removes duplicate pair contents. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def attemptEdges (attempts : List String) : List (String × String) :=
  attempts.flatMap observationPairs

def collectEdges : Expr := .listComp (.name "e")
  [("s", .name "attempts", []), ("e", .call (.name "edges_from") [.name "s"], [])]

theorem edges_source : executableBody
    ((findFunctionIn program.body "edges").getD ([], [])).2 =
      [.return (.call (.name "erase_dups") [collectEdges])] := rfl

theorem collect_edges_loop (heap : Mutable.Heap) (address collector : Nat)
    (attempts before remaining : List String) (collected : List Edge)
    (found : heap[address]? = some (.list (attempts.map text)))
    (edges : Edges heap collector collected) (distinct : address ≠ collector)
    (partition : attempts = before ++ remaining) (env : HeapCalls.Env) :
    ∃ after entries finalEnv,
      BlockContinues program env
        [.sequenceStepLoop "s" (.ref address) before.length (collectEdgeBody collector) []]
        heap finalEnv after ∧
      Edges after collector entries ∧ entries.map Prod.snd = collected.map Prod.snd ++
        attemptEdges remaining ∧ heap.length ≤ after.length ∧
      (∀ index < heap.length, index ≠ collector → after[index]? = heap[index]?) := by
  induction remaining generalizing heap before collected env with
  | nil =>
      refine ⟨heap, collected, env, ?_, edges, by simp [attemptEdges], le_rfl, by intros; rfl⟩
      apply BlockContinues.sequence_done (items := attempts.map text)
        (by simp [sequenceValue, Mutable.sequence, found])
      · simp [partition]
      · exact .nil
  | cons s rest ih =>
      let bound := setLocal env "s" (text s)
      obtain ⟨middle, current, middleEnv, stepped, currentEdges, currentPairs, grew, preserved⟩ :=
        collect_edge_step heap collector collected edges bound s (by simp [bound, setLocal])
      have input : middle[address]? = some (.list (attempts.map text)) :=
        (preserved address (List.getElem?_eq_some_iff.mp found).1 distinct).trans found
      obtain ⟨after, entries, finalEnv, continued, finalEdges, finalPairs, grewAgain, saved⟩ :=
        ih middle (before ++ [s]) current input currentEdges
          (by simpa [List.append_assoc] using partition) middleEnv
      refine ⟨after, entries, finalEnv, ?_, finalEdges, ?_, grew.trans grewAgain, ?_⟩
      · apply BlockContinues.sequence_step (items := attempts.map text) (value := text s)
          (by simp [sequenceValue, Mutable.sequence, found]) (by simp [partition])
        simpa [collectEdgeBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          bound] using stepped.append continued
      · rw [finalPairs, currentPairs]
        simp [attemptEdges, List.append_assoc]
      · intro index bounded different
        exact (saved index (lt_of_lt_of_le bounded grew) different).trans
          (preserved index bounded different)

theorem collect_edges_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getAttempts : env "attempts" = some (.ref address)) :
    ∃ after entries,
      Evaluates program env collectEdges heap (.ref heap.length) after ∧
      Edges after heap.length entries ∧ entries.map Prod.snd = attemptEdges attempts ∧
      heap <+: after := by
  have bounded := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨after, entries, finalEnv, collected, edges, contents, _, preserved⟩ :=
    collect_edges_loop (heap ++ [.list []]) address heap.length attempts [] attempts []
      (by simp [List.getElem?_append_left bounded, found])
      ⟨by simp, by simp⟩ (by omega) rfl
      (comprehensionEnv env
        [("s", .name "attempts", []), ("e", .call (.name "edges_from") [.name "s"], [])])
  refine ⟨after, entries, ?_, edges, by simpa using contents, ?_⟩
  · apply Evaluates.list_comp_sequence (items := attempts.map text)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getAttempts)
      (by simp [Mutable.sequence, found])
    exact collected
  · apply List.prefix_iff_getElem?.mpr
    intro index inside
    have retained := preserved index (by simp; omega) (by omega)
    simpa [List.getElem?_append_left inside, List.getElem?_eq_getElem inside] using retained

/-- Distinct logical edges retain their source tuple objects; the caller's heap is a prefix. -/
theorem edges_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text))) :
    ∃ after resultAddress entries,
      ReturnsValue program "edges" [.ref address] heap (.ref resultAddress) after ∧
      Edges after resultAddress entries ∧ (entries.map Prod.snd).Nodup ∧
      (∀ pair, pair ∈ entries.map Prod.snd ↔ pair ∈ attemptEdges attempts) ∧
      heap <+: after := by
  let source := (findFunctionIn program.body "edges").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref address] []
  obtain ⟨collectedHeap, collected, collectedSource, collectedEdges, contents, retained⟩ :=
    collect_edges_result heap address attempts found env rfl
  let entries := dedupBy Prod.snd [] collected
  let after := collectedHeap ++ [.list (entries.map edgeValue)]
  refine ⟨after, collectedHeap.length, entries, ?_, ?_, ?_, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.call (.cons collectedSource .nil)
      (dedup_edges collectedHeap heap.length collected collectedEdges)
  · exact dedup_edges_represents collectedHeap heap.length collected collectedEdges
  · exact dedupBy_unique Prod.snd [] collected (by simp)
  · intro pair
    simpa [entries, contents] using dedupBy_keys Prod.snd [] collected pair
  · exact retained.trans ⟨_, rfl⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Reference filters allocate fresh lists while retaining the original element references. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def filterBody (collector : Nat) (condition : Expr) (name : String) : List Stmt :=
  [.ifThen condition [.comprehensionAppend collector (.name name)] []]

theorem filter_loop {α : Type} (base : Mutable.Heap) (address : Nat) (items : List α)
    (encode : α → Mutable.Value) (predicate : α → Bool) (condition : Expr) (name : String)
    (found : base[address]? = some (.list (items.map encode))) (invariant : HeapCalls.Env → Prop)
    (preserved : ∀ env item, invariant env → invariant (setLocal env name (encode item)))
    (tested : ∀ env item (collected : List α), invariant env → item ∈ items →
      env name = some (encode item) → Evaluates program env condition
        (base ++ [.list (collected.map encode)]) (.scalar (.bool (predicate item)))
        (base ++ [.list (collected.map encode)]))
    (before remaining collected : List α) (partition : items = before ++ remaining)
    (env : HeapCalls.Env) (valid : invariant env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop name (.ref address) before.length
        (filterBody base.length condition name) []]
      (base ++ [.list (collected.map encode)]) finalEnv
      (base ++ [.list ((collected ++ remaining.filter predicate).map encode)]) ∧
      invariant finalEnv := by
  have input : (base ++ [.list (collected.map encode)])[address]? =
      some (.list (items.map encode)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  induction remaining generalizing before collected env with
  | nil =>
      refine ⟨env, ?_, valid⟩
      apply BlockContinues.sequence_done (items := items.map encode)
        (by simp [sequenceValue, Mutable.sequence, input])
      · simp [partition]
      · simpa using (BlockContinues.nil (module := program) (env := env)
          (heap := base ++ [.list (collected.map encode)]))
  | cons item rest ih =>
      let bound := setLocal env name (encode item)
      have boundValid : invariant bound := preserved env item valid
      have accepted := tested bound item collected boundValid (by simp [partition])
        (by simp [bound, setLocal])
      let next := if predicate item then collected ++ [item] else collected
      have emitted : BlockContinues program bound (filterBody base.length condition name)
          (base ++ [.list (collected.map encode)]) bound (base ++ [.list (next.map encode)]) := by
        cases flag : predicate item with
        | false =>
            simp only [next, flag, Bool.false_eq_true, if_false]
            exact BlockContinues.branch (flag := false)
              (by simpa only [flag] using accepted) rfl .nil
        | true =>
            simp only [next, flag, if_true]
            apply BlockContinues.branch (flag := true)
              (by simpa only [flag] using accepted) rfl
            have append := BlockContinues.comprehension_append (module := program) (globals := [])
              (env := bound) (expression := .name name) (address := base.length)
              (items := collected.map encode) (heap := base ++ [.list (collected.map encode)])
              (Evaluates.lookup (value := encode item) (by simp [bound, setLocal])) (by simp)
            simpa using append
      obtain ⟨finalEnv, continued, finalValid⟩ := ih (before ++ [item]) next
        (by simpa [List.append_assoc] using partition) bound boundValid
        (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]; exact found)
      refine ⟨finalEnv, ?_, finalValid⟩
      apply BlockContinues.sequence_step (items := items.map encode) (value := encode item)
        (by simp [sequenceValue, Mutable.sequence, input]) (by simp [partition])
      have combined := emitted.append continued
      cases flag : predicate item <;>
        simpa [filterBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          next, flag, List.append_assoc, bound] using combined

end data.«project-euler-statements».data.py.project_euler_statements.p79

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

/-! Sorting and filtering the reference node list preserve the least-ready selection invariant. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def nodeFilterTest : Expr := .compare (.name "n") [(.notEq, .name "found")]
def nodeFilter : Expr := .listComp (.name "n") [("n", .name "ns", [nodeFilterTest])]

theorem node_filter_source : (match (topoCode[2]? : Option Stmt) with
    | some (Stmt.whileDo _ body _) => body[3]?
    | _ => none) = some (.assign [.name "ns"] nodeFilter) := rfl

theorem node_filter_result (base : Mutable.Heap) (address : Nat) (nodes : List String)
    (found : base[address]? = some (.list (nodes.map text)))
    (env : HeapCalls.Env) (node : String) (getNodes : env "ns" = some (.ref address))
    (getFound : env "found" = some (text node)) :
    Evaluates program env nodeFilter base (.ref base.length)
      (base ++ [.list ((nodes.filter (fun item => decide (item ≠ node))).map text)]) := by
  let inner := comprehensionEnv env [("n", .name "ns", [nodeFilterTest])]
  let invariant := fun current : HeapCalls.Env => current "found" = some (text node)
  have valid : invariant inner := by
    simpa [invariant, inner, comprehensionEnv, setLocal] using getFound
  obtain ⟨finalEnv, filtered, _⟩ := filter_loop base address nodes text
    (fun item => decide (item ≠ node)) nodeFilterTest "n" found invariant
    (by intro current item bound; simpa [invariant, setLocal] using bound)
    (by
      intro current item collected bound _ lookup
      apply Evaluates.compare (Evaluates.lookup lookup) (Evaluates.lookup bound)
      simp [HeapCalls.compare, scalarCompare]) [] nodes [] rfl inner valid
  apply Evaluates.list_comp_sequence (items := nodes.map text)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getNodes)
    (by simp [Mutable.sequence, found])
  simpa only [List.length_nil, List.nil_append] using filtered

theorem node_filter_erase (nodes : List String) (node : String) (unique : nodes.Nodup) :
    nodes.filter (fun item => decide (item ≠ node)) = nodes.erase node := by
  rw [unique.erase_eq_filter]
  congr 1
  funext item
  simp [bne, beq_eq_decide]

theorem node_filter_sorted (nodes : List String) (node : String)
    (sorted : nodes.Pairwise (· ≤ ·)) :
    (nodes.filter (fun item => decide (item ≠ node))).Pairwise (· ≤ ·) :=
  sorted.sublist List.filter_sublist

theorem sort_nodes_result (heap : Mutable.Heap) (address : Nat) (nodes : List String)
    (found : heap[address]? = some (.list (nodes.map text)))
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref address)) :
    Evaluates program env (.builtinCall .sorted [.name "ns"]) heap (.ref heap.length)
      (heap ++ [.list ((ScalarSort.strings nodes).map text)]) := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getNodes) .nil)
  have sorted := primitive_sorted_list heap address (nodes.map Constant.string)
    ((ScalarSort.strings nodes).map Constant.string)
    (by simpa [List.map_map, Function.comp_def] using found) (ScalarSort.sort_strings nodes)
  simpa [List.map_map, Function.comp_def] using sorted

end data.«project-euler-statements».data.py.project_euler_statements.p79

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

/-! A successful reference iteration emits the least ready node and removes its constraints. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

structure TopoRoots where
  nodes : Nat
  edges : Nat
  output : Nat

structure TopoState (roots : TopoRoots) (nodes : List String) (entries : List Edge)
    (output : List String) (heap : Mutable.Heap) : Prop where
  nodesFound : heap[roots.nodes]? = some (.list (nodes.map text))
  edges : Edges heap roots.edges entries
  outputFound : heap[roots.output]? = some (.list (output.map text))
  nodesOutput : roots.nodes ≠ roots.output
  edgesOutput : roots.edges ≠ roots.output
  unique : nodes.Nodup
  sorted : nodes.Pairwise (· ≤ ·)

structure TopoBindings (roots : TopoRoots) (env : HeapCalls.Env) : Prop where
  nodes : env "ns" = some (.ref roots.nodes)
  edges : env "es" = some (.ref roots.edges)
  output : env "out" = some (.ref roots.output)

def cycleBody : List Stmt :=
  [.raise (some (.call (.name "ValueError")
    [.constant (.string "Constraints contain a cycle; no valid passcode exists.")]))]

def referenceStep : List Stmt :=
  [.assign [.name "found"] nextReady,
   .ifThen (.builtinCall .identity [.name "found", .constant .none]) cycleBody [],
   .expr (.call (.attribute (.name "out") "append") [.name "found"]),
   .assign [.name "ns"] nodeFilter,
   .assign [.name "es"] (.call (.name "remove_node") [.name "found", .name "es"])]

theorem reference_step_source : topoCode =
    [.assign [.name "ns"] (.builtinCall .sorted [.name "ns"]),
     .assign [.name "out"] (.list []),
     .whileDo (.name "ns") referenceStep [], .return (.name "out")] := rfl

def afterEmit (heap : Mutable.Heap) (roots : TopoRoots) (output : List String) (node : String) :=
  heap.set roots.output (.list ((output ++ [node]).map text))

def afterStep (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (node : String) : Mutable.Heap :=
  afterEmit heap roots output node ++
    [.list ((nodes.filter (fun item => decide (item ≠ node))).map text),
     .list ((entries.filter (retain node)).map edgeValue)]

def nextRoots (heap : Mutable.Heap) (roots : TopoRoots) : TopoRoots :=
  ⟨heap.length, heap.length + 1, roots.output⟩

def nextTopoEnv (heap : Mutable.Heap) (env : HeapCalls.Env) (node : String) : HeapCalls.Env :=
  setLocal (setLocal (setLocal env "found" (text node)) "ns" (.ref heap.length))
    "es" (.ref (heap.length + 1))

theorem output_write_edges (heap : Mutable.Heap) (roots : TopoRoots) (entries : List Edge)
    (output : List String) (node : String) (edges : Edges heap roots.edges entries)
    (found : heap[roots.output]? = some (.list (output.map text)))
    (distinct : roots.edges ≠ roots.output) :
    Edges (afterEmit heap roots output node) roots.edges entries := by
  constructor
  · simpa [afterEmit, List.getElem?_set, Ne.symm distinct] using edges.found
  · intro entry member
    have stored := edges.stored entry member
    have different : roots.output ≠ entry.1 := by
      intro same
      change heap[entry.1]? = _ at stored
      rw [← same, found] at stored
      cases stored
    simpa [Stored, afterEmit, List.getElem?_set, different] using stored

theorem step_result (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) (node : String)
    (selected : choose nodes (entries.map Prod.snd) = some node) :
    BlockContinues program env referenceStep heap (nextTopoEnv heap env node)
      (afterStep heap roots nodes entries output node) := by
  let chosen := setLocal env "found" (text node)
  let emitted := afterEmit heap roots output node
  let filtered := emitted ++ [.list ((nodes.filter (fun item => decide (item ≠ node))).map text)]
  have choice : Evaluates program env nextReady heap (text node) heap := by
    simpa only [selected, Option.map_some, Option.getD_some] using
      next_ready_choose heap roots.nodes roots.edges nodes entries state.nodesFound state.edges
        state.sorted env bindings.nodes bindings.edges
  have chooseStep : BlockContinues program env [.assign [.name "found"] nextReady]
      heap chosen heap := BlockContinues.assign choice
  have guard : BlockContinues program chosen
      [.ifThen (.builtinCall .identity [.name "found", .constant .none]) cycleBody []]
      heap chosen heap := by
    apply BlockContinues.branch (flag := false) (value := .scalar (.bool false))
      (Evaluates.builtin (values := [text node, .scalar .none])
        (.cons (Evaluates.lookup (by simp [chosen, setLocal])) (.cons Evaluates.constant .nil)) ?_)
      rfl .nil
    rfl
  have emittedStep : BlockContinues program chosen
      [.expr (.call (.attribute (.name "out") "append") [.name "found"])]
      heap chosen emitted := by
    apply BlockContinues.discard
    simpa [emitted, afterEmit, List.map_append] using
      Evaluates.append (module := program)
        (Evaluates.lookup (name := "out")
          (by simpa [chosen, setLocal] using bindings.output)) state.outputFound
        (Evaluates.lookup (name := "found") (by simp [chosen, setLocal])) state.outputFound
  have nodesFound : emitted[roots.nodes]? = some (.list (nodes.map text)) := by
    simpa [emitted, afterEmit, List.getElem?_set, Ne.symm state.nodesOutput] using state.nodesFound
  have edges := output_write_edges heap roots entries output node state.edges
    state.outputFound state.edgesOutput
  have filteredStep : BlockContinues program chosen [.assign [.name "ns"] nodeFilter]
      emitted (setLocal chosen "ns" (.ref heap.length)) filtered := by
    have evaluated := node_filter_result emitted roots.nodes nodes nodesFound chosen node
      (by simpa [chosen, setLocal] using bindings.nodes) (by simp [chosen, setLocal])
    simpa [filtered, emitted, afterEmit] using BlockContinues.assign (name := "ns") evaluated
  have removedStep : BlockContinues program (setLocal chosen "ns" (.ref heap.length))
      [.assign [.name "es"] (.call (.name "remove_node") [.name "found", .name "es"])]
      filtered (nextTopoEnv heap env node) (afterStep heap roots nodes entries output node) := by
    have called := Evaluates.call (env := setLocal chosen "ns" (.ref heap.length))
      (.cons (Evaluates.lookup (name := "found") (by simp [chosen, setLocal]))
        (.cons (Evaluates.lookup (name := "es")
          (by simpa [chosen, setLocal] using bindings.edges)) .nil))
      (remove_result filtered roots.edges entries (edges.append emitted _ roots.edges entries) node)
    simpa [nextTopoEnv, chosen, filtered, emitted, afterEmit, afterStep, List.append_assoc] using
      BlockContinues.assign (name := "es") called
  exact ((chooseStep.append guard).append emittedStep).append
    (filteredStep.append removedStep)

theorem step_state (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (node : String) :
    TopoState (nextRoots heap roots) (nodes.filter (fun item => decide (item ≠ node)))
      (entries.filter (retain node)) (output ++ [node])
      (afterStep heap roots nodes entries output node) := by
  have bounded : roots.output < heap.length :=
    (List.getElem?_eq_some_iff.mp state.outputFound).1
  have edges := output_write_edges heap roots entries output node state.edges
    state.outputFound state.edgesOutput
  constructor
  · simp [nextRoots, afterStep, afterEmit]
  · constructor
    · simp [nextRoots, afterStep, afterEmit]
    · intro edge member
      exact (edges.stored edge (List.mem_filter.mp member).1).append _ _ edge
  · simp [nextRoots, afterStep, afterEmit, List.getElem?_append_left, bounded]
  · simp only [nextRoots]; omega
  · simp only [nextRoots]; omega
  · exact state.unique.filter _
  · exact node_filter_sorted nodes node state.sorted

theorem step_bindings (heap : Mutable.Heap) (roots : TopoRoots) (env : HeapCalls.Env)
    (bindings : TopoBindings roots env) (node : String) :
    TopoBindings (nextRoots heap roots) (nextTopoEnv heap env node) := by
  constructor
  · simp [nextRoots, nextTopoEnv, setLocal]
  · simp [nextRoots, nextTopoEnv, setLocal]
  · simpa [nextRoots, nextTopoEnv, setLocal] using bindings.output

end data.«project-euler-statements».data.py.project_euler_statements.p79

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

/-! The reference loop terminates with the greedy ordering or its exact cycle exception. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def referenceLoop : Stmt := .whileDo (.name "ns") referenceStep []

def cycleException : ExceptionObject :=
  { typeName := "ValueError",
    args := [.string "Constraints contain a cycle; no valid passcode exists."] }

def referenceOutcome (address : Nat) : Option (List String) → Except ExceptionObject Mutable.Value
  | none => .error cycleException
  | some _ => .ok (.ref address)

theorem enter_reference_loop (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) (nonempty : nodes ≠ [])
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) :
    Reaches program anchors ⟨.block (referenceLoop :: following) env, stack, heap⟩
      ⟨.block (referenceStep ++ referenceLoop :: following) env, stack, heap⟩ := by
  apply Reaches.next rfl
  apply ((Evaluates.lookup (module := program) (heap := heap) bindings.nodes) anchors _).trans
  exact .next (by
    simp [HeapCalls.step, run, Mutable.truth, state.nodesFound, nonempty, referenceLoop,
      referenceStep, cycleBody, Calls.loopContinuation, Calls.loopControl,
      Calls.loopControlStmt]) .refl

theorem raise_cycle (heap : Mutable.Heap) (env : HeapCalls.Env) (following : List Stmt)
    (anchors : Nat) (stack : List HeapCalls.Frame := []) :
    Finishes (HeapCalls.step program anchors) ⟨.block (cycleBody ++ following) env, stack, heap⟩
      (.ok ⟨.error cycleException, [], heap, anchors⟩) := by
  refine Finishes.next (following := argumentsState (.raiseException "ValueError") env []
    [.constant (.string "Constraints contain a cycle; no valid passcode exists.")]
    stack heap) rfl ?_
  apply (Evaluates.arguments_reach
    (.cons (Evaluates.constant (module := program) (env := env)) .nil)
    (.raiseException "ValueError") [] anchors stack).finishes
  exact .done (by
    simp [HeapCalls.step, result, run, primitive, done, cycleException, protectGenerator,
      Calls.generatorException])

theorem no_choice_cycle (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env)
    (selected : choose nodes (entries.map Prod.snd) = none)
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame := []) :
    Finishes (HeapCalls.step program anchors)
      ⟨.block (referenceStep ++ following) env, stack, heap⟩
      (.ok ⟨.error cycleException, [], heap, anchors⟩) := by
  let chosen := setLocal env "found" (.scalar .none)
  have choice : Evaluates program env nextReady heap (.scalar .none) heap := by
    simpa only [selected, Option.map_none, Option.getD_none] using
      next_ready_choose heap roots.nodes roots.edges nodes entries state.nodesFound state.edges
        state.sorted env bindings.nodes bindings.edges
  have assigned := BlockContinues.assign (name := "found") choice
  apply (assigned (referenceStep.drop 1 ++ following) anchors stack).finishes
  have test : Evaluates program chosen (.builtinCall .identity [.name "found", .constant .none])
      heap (.scalar (.bool true)) heap :=
    Evaluates.builtin (values := [.scalar .none, .scalar .none])
      (.cons (Evaluates.lookup (by simp [chosen, setLocal]))
      (.cons Evaluates.constant .nil)) rfl
  refine Finishes.next rfl ((test anchors _).finishes ?_)
  exact .next (by simp [HeapCalls.step, run, Mutable.truth, scalarTruth, referenceStep, chosen])
    (raise_cycle heap chosen (referenceStep.drop 2 ++ following) anchors stack)

theorem step_untouched (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (node : String) (address : Nat)
    (bounded : address < heap.length) (different : address ≠ roots.output) :
    (afterStep heap roots nodes entries output node)[address]? = heap[address]? := by
  simp [afterStep, afterEmit, List.getElem?_append_left, bounded, Ne.symm different]

/-- The measure is the actual remaining node count, with no imposed search bound. -/
theorem reference_loop_context (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) :
    ∃ after finalOutput,
      SourceResult (.block [referenceLoop, .return (.name "out")] env) heap
        (referenceOutcome roots.output (order nodes (entries.map Prod.snd))) after ∧
      after[roots.output]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result →
        finalOutput = output ++ result) ∧
      (∀ address < heap.length, address ≠ roots.output → after[address]? = heap[address]?) := by
  by_cases empty : nodes = []
  · subst nodes
    have ordered : order ([] : List String) (entries.map Prod.snd) = some [] := by
      rw [order, if_pos rfl]
    refine ⟨heap, output, ?_, state.outputFound, ?_, by intros; rfl⟩
    · have exited := BlockContinues.while_loop (globals := [])
        (body := referenceStep) (otherwise := [])
        (Evaluates.lookup (module := program) (heap := heap) bindings.nodes)
        (show Mutable.truth (.ref roots.nodes) heap = some (.ok false, heap) by
          simp [Mutable.truth, state.nodesFound]) BlockContinues.nil
      have returned := BlockReturns.return_value (globals := []) (rest := [])
        (Evaluates.lookup (module := program) (heap := heap) bindings.output)
      simpa only [ordered, referenceOutcome] using exited.returns returned
    · intro result same
      have : result = [] := by simpa only [ordered, Option.some.injEq] using same.symm
      simp [this]
  · cases selected : choose nodes (entries.map Prod.snd) with
    | none =>
        have failed : order nodes (entries.map Prod.snd) = none := by
          rw [order, if_neg empty, selected]
        refine ⟨heap, output, ?_, state.outputFound, ?_, by intros; rfl⟩
        · rw [failed]
          intro anchors stack
          have entered := enter_reference_loop heap roots nodes entries output state env bindings
            empty [.return (.name "out")] anchors stack
          exact
            entered.finishes (no_choice_cycle heap roots nodes entries output state env bindings
              selected [referenceLoop, .return (.name "out")] anchors stack)
        · intro result same
          rw [failed] at same
          contradiction
    | some node =>
        have member := (choose_spec nodes (entries.map Prod.snd) node selected).1
        let remaining := nodes.filter (fun item => decide (item ≠ node))
        let retained := entries.filter (retain node)
        have shorter : remaining.length < nodes.length := by
          rw [show remaining = nodes.erase node from node_filter_erase nodes node state.unique,
            List.length_erase_of_mem member]
          have := List.length_pos_of_mem member
          omega
        let stepped := afterStep heap roots nodes entries output node
        let next := nextRoots heap roots
        let nextEnv := nextTopoEnv heap env node
        have nextState := step_state heap roots nodes entries output state node
        have nextBindings := step_bindings heap roots env bindings node
        obtain ⟨after, finalOutput, finished, found, agrees, untouched⟩ :=
          reference_loop_context stepped next remaining retained (output ++ [node])
            nextState nextEnv nextBindings
        have recurrence : order nodes (entries.map Prod.snd) =
            (order remaining (retained.map Prod.snd)).map (node :: ·) := by
          rw [order, if_neg empty, selected]
          change (order (nodes.erase node) (removeNode node (entries.map Prod.snd))).map _ = _
          rw [show remaining = nodes.erase node from node_filter_erase nodes node state.unique,
            remove_contents]
        have sameOutcome : referenceOutcome roots.output (order nodes (entries.map Prod.snd)) =
            referenceOutcome next.output (order remaining (retained.map Prod.snd)) := by
          rw [recurrence]
          cases order remaining (retained.map Prod.snd) <;> rfl
        refine ⟨after, finalOutput, ?_, found, ?_, ?_⟩
        · rw [sameOutcome]
          apply SourceResult.before _ _ heap stepped after _ _ finished
          intro anchors stack
          exact (enter_reference_loop heap roots nodes entries output state env bindings empty
            [.return (.name "out")] anchors stack).trans
              (step_result heap roots nodes entries output state env bindings node selected
                [referenceLoop, .return (.name "out")] anchors stack)
        · intro result same
          rw [recurrence] at same
          obtain ⟨rest, ordered, rfl⟩ := Option.map_eq_some_iff.mp same
          simpa only [List.append_assoc, List.singleton_append] using agrees rest ordered
        · intro address bounded different
          exact (untouched address (by
            simp only [stepped, afterStep, afterEmit, List.length_append, List.length_set,
              List.length_cons, List.length_nil]
            omega) different).trans
              (step_untouched heap roots nodes entries output node address bounded different)
termination_by nodes.length

theorem reference_loop_result (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) (anchors : Nat) :
    ∃ after finalOutput,
      Finishes (HeapCalls.step program anchors)
        ⟨.block [referenceLoop, .return (.name "out")] env, [], heap⟩
        (.ok ⟨referenceOutcome roots.output (order nodes (entries.map Prod.snd)), [],
          after, anchors⟩) ∧
      after[roots.output]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result →
        finalOutput = output ++ result) ∧
      (∀ address < heap.length, address ≠ roots.output → after[address]? = heap[address]?) := by
  obtain ⟨after, finalOutput, result, found, agrees, preserved⟩ :=
    reference_loop_context heap roots nodes entries output state env bindings
  exact ⟨after, finalOutput, result.finishes _ _ _ _ anchors, found, agrees, preserved⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The reference topological sort returns the least ordering without mutating its inputs. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def preparedHeap (heap : Mutable.Heap) (nodes : List String) : Mutable.Heap :=
  heap ++ [.list ((ScalarSort.strings nodes).map text), .list []]

def preparedRoots (heap : Mutable.Heap) (edgesAddress : Nat) : TopoRoots :=
  ⟨heap.length, edgesAddress, heap.length + 1⟩

def preparedEnv (heap : Mutable.Heap) (env : HeapCalls.Env) : HeapCalls.Env :=
  setLocal (setLocal env "ns" (.ref heap.length)) "out" (.ref (heap.length + 1))

theorem initialize_reference (heap : Mutable.Heap) (address : Nat) (nodes : List String)
    (found : heap[address]? = some (.list (nodes.map text)))
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref address)) :
    BlockContinues program env (topoCode.take 2) heap (preparedEnv heap env)
      (preparedHeap heap nodes) := by
  have sorted := BlockContinues.assign (name := "ns")
    (sort_nodes_result heap address nodes found env getNodes)
  have output := BlockContinues.assign (name := "out")
    (Evaluates.list (module := program) (globals := [])
      (env := setLocal env "ns" (.ref heap.length))
      (heap := heap ++ [.list ((ScalarSort.strings nodes).map text)]) .nil)
  simpa [preparedHeap, preparedEnv, List.append_assoc] using sorted.append output

theorem prepared_state (heap : Mutable.Heap) (edgesAddress : Nat) (nodes : List String)
    (entries : List Edge) (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup) :
    TopoState (preparedRoots heap edgesAddress) (ScalarSort.strings nodes) entries []
      (preparedHeap heap nodes) := by
  have bounded := (List.getElem?_eq_some_iff.mp edges.found).1
  constructor
  · simp [preparedHeap, preparedRoots]
  · exact edges.append heap _ edgesAddress entries
  · simp [preparedHeap, preparedRoots]
  · simp [preparedRoots]
  · simp only [preparedRoots]; omega
  · exact (ScalarSort.strings_perm nodes).nodup_iff.mpr unique
  · exact ProjectEulerStatements.StringSorting.strings_ordered nodes

theorem prepared_bindings (heap : Mutable.Heap) (edgesAddress : Nat) (env : HeapCalls.Env)
    (getEdges : env "es" = some (.ref edgesAddress)) :
    TopoBindings (preparedRoots heap edgesAddress) (preparedEnv heap env) := by
  constructor
  · simp [preparedRoots, preparedEnv, setLocal]
  · simpa [preparedRoots, preparedEnv, setLocal] using getEdges
  · simp [preparedRoots, preparedEnv, setLocal]

/-- Node enumeration order is irrelevant; every original heap cell is preserved. -/
theorem reference_body_context (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup)
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref nodesAddress))
    (getEdges : env "es" = some (.ref edgesAddress)) :
    ∃ after finalOutput,
      SourceResult (.block topoCode env) heap
        (referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd))) after ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  obtain ⟨after, finalOutput, completed, outputFound, agrees, untouched⟩ :=
    reference_loop_context (preparedHeap heap nodes) (preparedRoots heap edgesAddress)
      (ScalarSort.strings nodes) entries []
      (prepared_state heap edgesAddress nodes entries edges unique)
      (preparedEnv heap env) (prepared_bindings heap edgesAddress env getEdges)
  have same : order (ScalarSort.strings nodes) (entries.map Prod.snd) =
      order nodes (entries.map Prod.snd) :=
    order_nodes_perm _ _ _ (ScalarSort.strings_perm nodes)
  refine ⟨after, finalOutput, ?_, outputFound, ?_, ?_⟩
  · have combined := SourceResult.before _ _ heap (preparedHeap heap nodes) after _
      (fun anchors stack => initialize_reference heap nodesAddress nodes found env getNodes
        [referenceLoop, .return (.name "out")] anchors stack) completed
    simpa only [same] using combined
  · intro result ordered
    simpa only [List.nil_append] using agrees result (same.trans ordered)
  · intro address bounded
    have saved := untouched address (by simp [preparedHeap]; omega)
      (by simp [preparedRoots]; omega)
    simpa [preparedHeap, List.getElem?_append_left, bounded] using saved

theorem reference_body_result (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup)
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref nodesAddress))
    (getEdges : env "es" = some (.ref edgesAddress)) (anchors : Nat) :
    ∃ after finalOutput,
      Finishes (HeapCalls.step program anchors) ⟨.block topoCode env, [], heap⟩
        (.ok ⟨referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd)), [],
          after, anchors⟩) ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  obtain ⟨after, finalOutput, result, contents, agrees, preserved⟩ :=
    reference_body_context heap nodesAddress edgesAddress nodes entries found edges unique
      env getNodes getEdges
  exact ⟨after, finalOutput, SourceResult.finishes _ _ _ _ result anchors,
    contents, agrees, preserved⟩

/-- The call result composes with an enclosing expression or statement in either outcome. -/
theorem reference_call_context (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup) :
    ∃ after finalOutput,
      SourceResult (.operation (.call "topo") [.ref nodesAddress, .ref edgesAddress]) heap
        (referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd))) after ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  let source := (findFunctionIn program.body "topo").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref nodesAddress, .ref edgesAddress] []
  obtain ⟨after, output, completed, contents, agrees, preserved⟩ :=
    reference_body_context heap nodesAddress edgesAddress nodes entries found edges unique
      env rfl rfl
  refine ⟨after, output, ?_, contents, agrees, preserved⟩
  exact SourceResult.before _ _ heap heap after _ (fun _ _ => .next rfl .refl) completed

/-- This is the source function call, including normal and exceptional completion. -/
theorem reference_call_result (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup) :
    ∃ after finalOutput,
      (HeapCalls.call program "topo" [.ref nodesAddress, .ref edgesAddress] heap).Finishes
        ⟨referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd)), [],
          after, heap.length⟩ ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  let source := (findFunctionIn program.body "topo").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref nodesAddress, .ref edgesAddress] []
  obtain ⟨after, output, completed, contents, agrees, preserved⟩ :=
    reference_body_result heap nodesAddress edgesAddress nodes entries found edges unique
      env rfl rfl heap.length
  exact ⟨after, output, .next rfl completed, contents, agrees, preserved⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The reference builds the node and edge arguments in Python's left-to-right evaluation order. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def graphArguments : List Expr :=
  [.call (.name "nodes") [.name "checked"], .call (.name "edges") [.name "checked"]]

theorem naive_return_source : (executableBody
    ((findFunctionIn program.body "naive").getD ([], [])).2).getLast? =
    some (.return (.call (.attribute (.constant (.string "")) "join")
      [.call (.name "topo") graphArguments])) := rfl

theorem heap_prefix_lookup (heap after : Mutable.Heap) (retained : heap <+: after)
    (address : Nat) (object : Mutable.Object) (found : heap[address]? = some object) :
    after[address]? = some object := by
  obtain ⟨extra, rfl⟩ := retained
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem graph_arguments (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref address)) :
    ∃ after edgesAddress entries,
      Evaluates.Arguments program env graphArguments heap
        [.ref (heap.length + 1), .ref edgesAddress] after ∧
      after[heap.length + 1]? = some (.list ((nodeValues attempts).map text)) ∧
      Edges after edgesAddress entries ∧ (entries.map Prod.snd).Nodup ∧
      (∀ pair, pair ∈ entries.map Prod.snd ↔ pair ∈ attemptEdges attempts) ∧
      heap <+: after := by
  let middle := heap ++ [.list ((attemptCharacters attempts).map text),
    .list ((nodeValues attempts).map text)]
  have initial : heap <+: middle := ⟨_, rfl⟩
  have input := heap_prefix_lookup heap middle initial address _ found
  obtain ⟨after, edgesAddress, entries, executed, edges, unique, contents, retained⟩ :=
    edges_result middle address attempts input
  refine ⟨after, edgesAddress, entries, ?_, ?_, edges, unique, contents, initial.trans retained⟩
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup getChecked) .nil)
      (nodes_result heap address attempts found))
        (.cons (Evaluates.call (.cons (Evaluates.lookup getChecked) .nil) executed) .nil)
  · apply heap_prefix_lookup middle after retained
    simp [middle]

def tripleText (triple : Char × Char × Char) : String :=
  String.ofList [triple.1, triple.2.1, triple.2.2]

def tripleSymbols (triple : Char × Char × Char) : String × String × String :=
  (character triple.1, character triple.2.1, character triple.2.2)

/-- The reference's extra first-to-third edge is redundant, including cyclic observations. -/
theorem reference_order_adjacent (triples : List (Char × Char × Char)) :
    order (nodeValues (triples.map tripleText)) (attemptEdges (triples.map tripleText)) =
      order (nodeValues (triples.map tripleText)) (adjacentEdges (triples.map tripleSymbols)) := by
  have pairs : attemptEdges (triples.map tripleText) =
      expandedEdges (triples.map tripleSymbols) := by
    simp [attemptEdges, observationPairs, expandedEdges, tripleText, tripleSymbols,
      List.flatMap_map]
  rw [pairs]
  apply order_expansion
  intro symbols member
  obtain ⟨triple, present, rfl⟩ := List.mem_map.mp member
  have characterPresent (c : Char) (position : c ∈ [triple.1, triple.2.1, triple.2.2]) :
      character c ∈ nodeValues (triples.map tripleText) := by
    apply (node_values_mem _ _).mpr
    refine ⟨tripleText triple, List.mem_map.mpr ⟨triple, present, rfl⟩, c, ?_, rfl⟩
    simpa [tripleText] using position
  exact ⟨characterPresent triple.1 (by simp), characterPresent triple.2.1 (by simp),
    characterPresent triple.2.2 (by simp)⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The reference's final expression builds the graph, orders it, and joins its characters. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def checkedExpression : Expr := .call (.attribute (.constant (.string "")) "join")
  [.call (.name "topo") graphArguments]

def checkedOutcome (attempts : List String) : Except ExceptionObject Mutable.Value :=
  match order (nodeValues attempts) (attemptEdges attempts) with
  | none => .error cycleException
  | some output => .ok (text (String.intercalate "" output))

theorem checked_expression_source : (executableBody
    ((findFunctionIn program.body "naive").getD ([], [])).2).getLast? =
      some (.return checkedExpression) := naive_return_source

theorem checked_expression_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref address)) :
    ∃ after, SourceResult (.expr checkedExpression env) heap (checkedOutcome attempts) after ∧
      heap <+: after := by
  obtain ⟨middle, edgeAddress, entries, arguments, nodesFound, edges, _, contents, retained⟩ :=
    graph_arguments heap address attempts found env getChecked
  obtain ⟨after, output, called, outputFound, agrees, untouched⟩ :=
    reference_call_context middle (heap.length + 1) edgeAddress (nodeValues attempts) entries
      nodesFound edges (node_values_unique attempts)
  have sameOrder : order (nodeValues attempts) (entries.map Prod.snd) =
      order (nodeValues attempts) (attemptEdges attempts) :=
    order_edges_congr _ _ _ contents
  have evaluated := source_call env "topo" graphArguments heap middle after
    [.ref (heap.length + 1), .ref edgeAddress]
    (referenceOutcome (middle.length + 1) (order (nodeValues attempts) (attemptEdges attempts)))
    arguments (by simpa only [sameOrder] using called)
  refine ⟨after, ?_, retained.trans ?_⟩
  · cases ordered : order (nodeValues attempts) (attemptEdges attempts) with
    | none =>
        simp only [checkedOutcome, ordered]
        intro anchors stack
        have failed := evaluated anchors
          (.arguments (.join "") [] [] env :: stack)
        simp only [ordered, referenceOutcome] at failed
        refine Finishes.next rfl (Finishes.next rfl ?_)
        exact .next (by simp [HeapCalls.step, run, bindMethod, argumentsState]) failed
    | some result =>
        have listFound : after[middle.length + 1]? = some (.list (result.map text)) := by
          rw [agrees result (sameOrder.trans ordered)] at outputFound
          exact outputFound
        have successful : Evaluates program env (.call (.name "topo") graphArguments)
            heap (.ref (middle.length + 1)) after := by
          simpa only [ordered, referenceOutcome] using evaluated
        have joined := Evaluates.join (module := program) (globals := [])
          Evaluates.constant (.cons successful .nil)
          (primitive_join_list after (middle.length + 1) "" result listFound)
          (by intros; contradiction)
        simpa only [checkedOutcome, ordered] using joined
  · apply List.prefix_iff_getElem?.mpr
    intro index bounded
    simpa only [List.getElem?_eq_getElem bounded] using untouched index bounded

theorem checked_return_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref address)) :
    ∃ after, SourceResult (.block [.return checkedExpression] env) heap
      (checkedOutcome attempts) after ∧ heap <+: after := by
  obtain ⟨after, evaluated, retained⟩ := checked_expression_result heap address attempts found
    env getChecked
  exact ⟨after, SourceResult.before _ _ heap heap after _
    (fun _ _ => .next rfl .refl) evaluated, retained⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Validation preserves the accepted prefix and raises the first malformed attempt's error. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def invalidTest : Expr := .boolOp .or
  [.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))],
   .unaryOp .not (.call (.attribute (.name "attempt") "isdigit") [])]

def invalidMessage : Expr :=
  .binOp (.binOp (.constant (.string "")) .add (.constant (.string "Invalid attempt: ")))
    .add (.builtinCall .repr [.name "attempt"])

def invalidException (s : String) : ExceptionObject :=
  { typeName := "ValueError"
    args := [.string ("Invalid attempt: " ++ Strings.reprValue (.string s))] }

def invalidBody : List Stmt :=
  [.raise (some (.call (.name "ValueError") [invalidMessage]))]

def appendAttempt : List Stmt :=
  [.expr (.call (.attribute (.name "checked") "append") [.name "attempt"])]

def validationBody : List Stmt := [.ifThen invalidTest invalidBody []] ++ appendAttempt

def validationLoop (source : SequenceSource) (position : Nat) : Stmt :=
  .sequenceStepLoop "attempt" source position validationBody []

def naiveCode : List Stmt := executableBody
  ((findFunctionIn program.body "naive").getD ([], [])).2

theorem naive_source : naiveCode =
    [.annAssign (.name "checked") (.subscript (.name "list") (.name "str"))
       (some (.list [])),
     .forIn (.name "attempt") (.name "attempts") validationBody [],
     .return checkedExpression] := rfl

theorem valid_guard (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) (length : s.length = 3)
    (digits : Strings.isDigit s = true) :
    BlockContinues program env [.ifThen invalidTest invalidBody []] heap env heap := by
  have sized : Evaluates program env (.builtinCall .len [.name "attempt"])
      heap (number 3) heap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getS) .nil)
    simp [primitive, Mutable.length, length, number, text]
  have compared : Evaluates program env
      (.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))])
      heap (.scalar (.bool false)) heap := by
    exact Evaluates.compare sized Evaluates.constant rfl
  have tested : Evaluates program env (.call (.attribute (.name "attempt") "isdigit") [])
      heap (.scalar (.bool true)) heap := by
    simpa only [digits] using Evaluates.is_digit (module := program)
      (Evaluates.lookup (heap := heap) getS)
      (by intro name equal; cases equal; simp [getS])
  have negated : Evaluates program env
      (.unaryOp .not (.call (.attribute (.name "attempt") "isdigit") []))
      heap (.scalar (.bool false)) heap := Evaluates.unary tested rfl
  have condition : Evaluates program env invalidTest heap (.scalar (.bool false)) heap :=
    Evaluates.boolean_next compared rfl rfl (Evaluates.boolean_last negated rfl)
  exact BlockContinues.branch condition rfl .nil

theorem invalid_guard (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) :
    Evaluates program env invalidTest heap (.scalar (.bool true)) heap := by
  have sized : Evaluates program env (.builtinCall .len [.name "attempt"])
      heap (number s.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup getS) .nil) rfl
  by_cases length : s.length = 3
  · have digits : Strings.isDigit s = false := invalid.resolve_left (by simpa using length)
    have compared : Evaluates program env
        (.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))])
        heap (.scalar (.bool false)) heap := by
      apply Evaluates.compare sized Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, length]
    have tested : Evaluates program env (.call (.attribute (.name "attempt") "isdigit") [])
        heap (.scalar (.bool false)) heap := by
      simpa only [digits] using Evaluates.is_digit (module := program)
        (Evaluates.lookup (heap := heap) getS)
        (by intro name equal; cases equal; simp [getS])
    have negated : Evaluates program env
        (.unaryOp .not (.call (.attribute (.name "attempt") "isdigit") []))
        heap (.scalar (.bool true)) heap := Evaluates.unary tested rfl
    exact Evaluates.boolean_next compared rfl rfl (Evaluates.boolean_last negated rfl)
  · have compared : Evaluates program env
        (.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))])
        heap (.scalar (.bool true)) heap := by
      apply Evaluates.compare sized Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      omega
    exact Evaluates.boolean_stop compared rfl rfl

theorem invalid_message (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) :
    Evaluates program env invalidMessage heap
      (text ("Invalid attempt: " ++ Strings.reprValue (.string s))) heap := by
  have messageStart : Evaluates program env
      (.binOp (.constant (.string "")) .add (.constant (.string "Invalid attempt: ")))
      heap (text "Invalid attempt: ") heap :=
    Evaluates.binary Evaluates.constant Evaluates.constant rfl
  exact Evaluates.binary messageStart (Evaluates.repr (Evaluates.lookup getS)) rfl

theorem invalid_body (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) (following : List Stmt) (anchors : Nat)
    (stack : List HeapCalls.Frame) :
    Finishes (step program anchors) ⟨.block (invalidBody ++ following) env, stack, heap⟩
      (.ok ⟨.error (invalidException s), [], heap, anchors⟩) := by
  change Finishes (step program anchors)
    ⟨.block ((.raise (some (.call (.name "ValueError") [invalidMessage]))) :: following) env,
      stack, heap⟩ (.ok ⟨.error (invalidException s), [], heap, anchors⟩)
  refine Finishes.next (following :=
    argumentsState (.raiseException "ValueError") env [] [invalidMessage] stack heap) ?_ ?_
  · rfl
  apply (Evaluates.arguments_reach
    (.cons (invalid_message env heap s getS) .nil) (.raiseException "ValueError") []
    anchors stack).finishes
  exact Finishes.done (by
    simp [step, result, run, primitive, done, protectGenerator,
      Calls.generatorException, invalidException, text])

theorem accepted_attempt (base : Mutable.Heap) (checked : List String)
    (env : HeapCalls.Env) (s : String)
    (getChecked : env "checked" = some (.ref base.length))
    (getAttempt : env "attempt" = some (text s))
    (length : s.length = 3) (digits : Strings.isDigit s = true) :
    BlockContinues program env validationBody (base ++ [.list (checked.map text)]) env
      (base ++ [.list ((checked ++ [s]).map text)]) := by
  apply (valid_guard env _ s getAttempt length digits).append
  apply BlockContinues.discard
  have appended := Evaluates.append (module := program) (globals := [])
    (value := text s) (current := checked.map text)
    (Evaluates.lookup (name := "checked") getChecked)
    (show (base ++ [.list (checked.map text)])[base.length]? =
      some (.list (checked.map text)) by simp)
    (Evaluates.lookup (name := "attempt") getAttempt) (by simp)
  simpa [List.map_append] using appended

theorem rejected_attempt (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getAttempt : env "attempt" = some (text s))
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (following : List Stmt) :
    SourceResult (.block (validationBody ++ following) env) heap
      (.error (invalidException s)) heap := by
  intro anchors stack
  refine Finishes.next (following := ⟨.expr invalidTest env,
    .branch invalidBody [] (appendAttempt ++ following) env :: stack, heap⟩) rfl ?_
  apply (invalid_guard env heap s getAttempt invalid anchors _).finishes
  refine Finishes.next (following :=
    ⟨.block (invalidBody ++ (appendAttempt ++ following)) env, stack, heap⟩) ?_ ?_
  · simp [step, run, Mutable.truth, scalarTruth]
  exact invalid_body env heap s getAttempt _ anchors stack

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The complete reference body for stable sequence inputs, including validation and cycles. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

/-- The caller's input remains readable when the reference allocates private lists. -/
structure SequenceInput (base : Mutable.Heap) (source : SequenceSource)
    (attempts : List String) : Prop where
  read : ∀ heap, base <+: heap →
    Mutable.sequence (sequenceValue source) heap = some (.ok (attempts.map text), heap)

theorem SequenceInput.list (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.list (attempts.map text))) :
    SequenceInput base (.ref address) attempts := by
  constructor
  intro heap saved
  obtain ⟨suffix, rfl⟩ := saved
  have retained : (base ++ suffix)[address]? = some (.list (attempts.map text)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simp [sequenceValue, Mutable.sequence, retained]

theorem SequenceInput.tuple (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.tuple (attempts.map text))) :
    SequenceInput base (.ref address) attempts := by
  constructor
  intro heap saved
  obtain ⟨suffix, rfl⟩ := saved
  have retained : (base ++ suffix)[address]? = some (.tuple (attempts.map text)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simp [sequenceValue, Mutable.sequence, retained]

def validatedOutcome (checked : List String) : List String → Except ExceptionObject Mutable.Value
  | [] => checkedOutcome checked
  | s :: rest =>
      if s.length = 3 ∧ Strings.isDigit s = true then validatedOutcome (checked ++ [s]) rest
      else .error (invalidException s)

theorem validatedOutcome_prefix (checked accepted rest : List String)
    (valid : ∀ s ∈ accepted, s.length = 3 ∧ Strings.isDigit s = true) :
    validatedOutcome checked (accepted ++ rest) = validatedOutcome (checked ++ accepted) rest := by
  induction accepted generalizing checked with
  | nil => simp
  | cons s tail ih =>
      have head := valid s (by simp)
      have later : ∀ s ∈ tail, s.length = 3 ∧ Strings.isDigit s = true :=
        fun s member => valid s (List.mem_cons_of_mem _ member)
      simp only [List.cons_append, validatedOutcome, if_pos head,
        ih _ later, List.append_assoc, List.nil_append]

theorem validatedOutcome_valid (attempts : List String)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true) :
    validatedOutcome [] attempts = checkedOutcome attempts := by
  simpa only [List.append_nil, List.nil_append, validatedOutcome] using
    validatedOutcome_prefix [] attempts [] valid

theorem validatedOutcome_first_error (accepted rest : List String) (s : String)
    (valid : ∀ s ∈ accepted, s.length = 3 ∧ Strings.isDigit s = true)
    (invalid : ¬ (s.length = 3 ∧ Strings.isDigit s = true)) :
    validatedOutcome [] (accepted ++ s :: rest) = .error (invalidException s) := by
  rw [validatedOutcome_prefix [] accepted (s :: rest) valid]
  simp only [validatedOutcome, if_neg invalid]

theorem validation_enter (base : Mutable.Heap) (source : SequenceSource)
    (attempts before rest : List String) (s : String)
    (input : SequenceInput base source attempts) (partition : attempts = before ++ s :: rest)
    (heap : Mutable.Heap) (saved : base <+: heap) (env : HeapCalls.Env)
    (following : List Stmt) (anchors : Nat) (stack : List Frame) :
    Reaches program anchors
      ⟨.block ([validationLoop source before.length] ++ following) env, stack, heap⟩
      ⟨.block (validationBody ++ ([validationLoop source (before.length + 1)] ++ following))
        (setLocal env "attempt" (text s)), stack, heap⟩ := by
  have item : (attempts.map text)[before.length]? = some (text s) := by simp [partition]
  exact .next (by
    simp [validationLoop, step, run, input.read heap saved, item, List.append_assoc]
    rfl) .refl

theorem validated_sequence (base : Mutable.Heap) (source : SequenceSource)
    (attempts : List String) (input : SequenceInput base source attempts)
    (remaining before checked : List String) (partition : attempts = before ++ remaining)
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref base.length)) :
    ∃ after, SourceResult
      (.block [validationLoop source before.length, .return checkedExpression] env)
      (base ++ [.list (checked.map text)]) (validatedOutcome checked remaining) after ∧
      base <+: after := by
  induction remaining generalizing before checked env with
  | nil =>
      obtain ⟨after, returned, saved⟩ := checked_return_result
        (base ++ [.list (checked.map text)]) base.length checked (by simp) env getChecked
      refine ⟨after, ?_, (List.prefix_append _ _).trans saved⟩
      apply SourceResult.before _ _ _ _ _ _ _ returned
      intro anchors stack
      have noItem : (attempts.map text)[before.length]? = none := by simp [partition]
      exact .next (by simp [validationLoop, step, run,
        input.read _ (List.prefix_append _ _), noItem]) .refl
  | cons s rest ih =>
      let bound := setLocal env "attempt" (text s)
      have boundChecked : bound "checked" = some (.ref base.length) := by
        simpa [bound, setLocal] using getChecked
      have boundAttempt : bound "attempt" = some (text s) := by simp [bound, setLocal]
      have entered := validation_enter base source attempts before rest s input partition
        (base ++ [.list (checked.map text)]) (List.prefix_append _ _) env
        [.return checkedExpression]
      by_cases valid : s.length = 3 ∧ Strings.isDigit s = true
      · simp only [validatedOutcome, if_pos valid]
        obtain ⟨after, continued, saved⟩ := ih (before ++ [s]) (checked ++ [s])
          (by simpa [List.append_assoc] using partition) bound boundChecked
        have iteration := accepted_attempt base checked bound s boundChecked boundAttempt
          valid.1 valid.2
        refine ⟨after, ?_, saved⟩
        apply SourceResult.before _ _ _ _ _ _ _
          (show SourceResult
            (.block [validationLoop source (before.length + 1), .return checkedExpression] bound)
            (base ++ [.list ((checked ++ [s]).map text)])
            (validatedOutcome (checked ++ [s]) rest) after from by simpa using continued)
        intro anchors stack
        exact (entered anchors stack).trans
          (iteration [validationLoop source (before.length + 1), .return checkedExpression]
            anchors stack)
      · simp only [validatedOutcome, if_neg valid]
        refine ⟨base ++ [.list (checked.map text)], ?_, List.prefix_append _ _⟩
        apply SourceResult.before _ _ _ _ _ _ entered
        apply rejected_attempt bound _ s boundAttempt
        by_cases length : s.length = 3
        · exact Or.inr (by simpa [length] using valid)
        · exact Or.inl length

theorem naive_body_result (base : Mutable.Heap) (value : Mutable.Value)
    (attempts : List String) (input : SequenceInput base (sequenceSource value) attempts)
    (env : HeapCalls.Env) (getInput : env "attempts" = some value) :
    ∃ after, SourceResult (.block naiveCode env) base (validatedOutcome [] attempts) after ∧
      base <+: after := by
  let bound := setLocal env "checked" (.ref base.length)
  let heap := base ++ [.list []]
  obtain ⟨after, result, saved⟩ := validated_sequence base (sequenceSource value) attempts input
    attempts [] [] rfl bound (by simp [bound, setLocal])
  refine ⟨after, ?_, saved⟩
  apply SourceResult.before _ _ _ _ _ _ _ result
  intro anchors stack
  rw [naive_source]
  have allocated : BlockContinues program env
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str"))
        (some (.list []))] base bound heap :=
    BlockContinues.annAssign (Evaluates.list .nil)
  apply (allocated
    [.forIn (.name "attempt") (.name "attempts") validationBody [], .return checkedExpression]
    anchors stack).trans
  have lookup : bound "attempts" = some value := by simpa [bound, setLocal] using getInput
  have read : Mutable.sequence value heap = some (.ok (attempts.map text), heap) := by
    simpa only [sequenceValue_source] using input.read heap (List.prefix_append _ _)
  apply Reaches.next rfl
  apply (Evaluates.lookup (module := program) lookup anchors _).trans
  exact .next (by simp [step, run, read, validationLoop, heap]) .refl

abbrev naiveArgs : List Arg := ((findFunctionIn program.body "naive").getD ([], [])).1
abbrev naiveBody : List Stmt := ((findFunctionIn program.body "naive").getD ([], [])).2

theorem naive_call_result (base : Mutable.Heap) (value : Mutable.Value)
    (attempts : List String) (input : SequenceInput base (sequenceSource value) attempts) :
    ∃ after, SourceResult (.operation (.call "naive") [value]) base
      (validatedOutcome [] attempts) after ∧ base <+: after := by
  obtain ⟨after, result, saved⟩ := naive_body_result base value attempts input
    (functionEnv naiveArgs naiveBody [value] []) rfl
  exact ⟨after, SourceResult.before _ _ _ _ _ _ (fun _ _ => .next rfl .refl) result, saved⟩

theorem naive_sequence_finishes (base : Mutable.Heap) (value : Mutable.Value)
    (attempts : List String) (input : SequenceInput base (sequenceSource value) attempts) :
    ∃ after, (call program "naive" [value] base).Finishes
      ⟨validatedOutcome [] attempts, [], after, base.length⟩ ∧ base <+: after := by
  obtain ⟨after, result, saved⟩ := naive_call_result base value attempts input
  exact ⟨after, SourceResult.finishes _ _ _ _ result base.length, saved⟩

theorem naive_list_finishes (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.list (attempts.map text))) :
    ∃ after, (call program "naive" [.ref address] base).Finishes
      ⟨validatedOutcome [] attempts, [], after, base.length⟩ ∧ base <+: after :=
  naive_sequence_finishes base (.ref address) attempts
    (SequenceInput.list base address attempts found)

theorem naive_tuple_finishes (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.tuple (attempts.map text))) :
    ∃ after, (call program "naive" [.ref address] base).Finishes
      ⟨validatedOutcome [] attempts, [], after, base.length⟩ ∧ base <+: after :=
  naive_sequence_finishes base (.ref address) attempts
    (SequenceInput.tuple base address attempts found)

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Set traversal selects the first validation error in the actual reference call. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev setValidationEnv (value : Mutable.Value) : HeapCalls.Env :=
  functionEnv naiveArgs naiveBody [value] []

theorem naive_set_failure_mod (heap : Mutable.Heap) (address index : Nat) (items : List Constant)
    (s : String) (choices : ChoiceSchedule)
    (found : heap[address]? = some (.set items)) (selected : items[index]? = some (.string s))
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) (choice : choices 0 % items.length = index) :
    ((SetCalls.call program "naive" [.ref address] heap).run choices).Finishes
      ⟨.error (invalidException s), [], heap ++ [.list []], heap.length⟩ := by
  let env := setValidationEnv (.ref address)
  let bound := setLocal env "checked" (.ref heap.length)
  let after := heap ++ [Mutable.Object.list []]
  have allocated : BlockContinues program env
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str")) (some (.list []))]
      heap bound after := BlockContinues.annAssign (Evaluates.list .nil)
  have saved : after[address]? = some (.set items) := by
    simpa only [after, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found
  change Finishes (SetCalls.step program heap.length choices)
    ⟨⟨.operation (.call "naive") [.ref address], [], heap⟩, 0⟩ _
  apply SetCalls.Reaches.finishes (SetCalls.Reaches.of_heap
    (show HeapCalls.Reaches program heap.length
      ⟨.operation (.call "naive") [.ref address], [], heap⟩ ⟨.block naiveCode env, [], heap⟩ from .next rfl .refl)
    choices 0)
  rw [naive_source]
  apply (SetCalls.Reaches.of_heap (allocated _ heap.length []) choices 0).finishes
  apply (SetCalls.for_set_name program choices heap.length 0 address after items bound "attempt" "attempts"
    validationBody [] [.return checkedExpression] [] (by rfl) saved).finishes
  apply Finishes.next (SetCalls.select_item_mod program choices heap.length 0 address index after items items (.string s)
    bound "attempt" validationBody [] [.return checkedExpression] [] saved selected choice)
  exact SetCalls.finishes_of_heap (rejected_attempt (setLocal bound "attempt" (.scalar (.string s))) after s
    (by simp [setLocal, text]) invalid _ heap.length []) choices 1

theorem naive_set_failure (heap : Mutable.Heap) (address index : Nat) (items : List Constant)
    (s : String) (choices : ChoiceSchedule)
    (found : heap[address]? = some (.set items)) (selected : items[index]? = some (.string s))
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) (choice : choices 0 = index) :
    ((SetCalls.call program "naive" [.ref address] heap).run choices).Finishes
      ⟨.error (invalidException s), [], heap ++ [.list []], heap.length⟩ := by
  exact naive_set_failure_mod heap address index items s choices found selected invalid
    (by rw [choice]; exact Nat.mod_eq_of_lt (List.getElem?_eq_some_iff.mp selected).1)

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Reference validation consumes actual iterator methods and preserves their shared effects. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

/-- The checked list may be anywhere in the heap, with later iterator allocations after it. -/
theorem accepted_attempt_at (heap : Mutable.Heap) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (s : String)
    (found : heap[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (getAttempt : env "attempt" = some (text s))
    (length : s.length = 3) (digits : Strings.isDigit s = true) :
    BlockContinues program env validationBody heap env
      (heap.set address (.list ((checked ++ [s]).map text))) := by
  apply (valid_guard env heap s getAttempt length digits).append
  apply BlockContinues.discard
  have appended := Evaluates.append (module := program) (globals := [])
    (value := text s) (current := checked.map text)
    (Evaluates.lookup (name := "checked") getChecked) found
    (Evaluates.lookup (name := "attempt") getAttempt) found
  simpa [List.map_append] using appended

abbrev validationIteratorLoop (env : HeapCalls.Env) (following : List Stmt)
    (stack : List HeapCalls.Frame) : IteratorCalls.Loop :=
  ⟨"attempt", validationBody, [], following, env, stack⟩

theorem iterator_accepted_attempt (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) := by
  have body := accepted_attempt_at yielded address checked (setLocal env "attempt" (text s)) s
    found (by simpa [setLocal] using getChecked) (by simp [setLocal]) length digits
  exact IteratorCalls.advance_continue (loop := validationIteratorLoop env following stack)
    isObject bound executed rfl (body.extend extension)

/-- The only reference-body write is to its private checked list. -/
theorem iterator_accepted_preserves (heap : Mutable.Heap) (address observed : Nat)
    (checked : List String) (s : String) (separate : address ≠ observed) :
    (heap.set address (.list ((checked ++ [s]).map text)))[observed]? = heap[observed]? := by
  simp [separate]

/-- Reference validation cannot alter the empty-tuple identity seen by the iterator. -/
theorem iterator_accepted_emptyTuple (heap : Mutable.Heap) (address : Nat)
    (checked : List String) (s : String)
    (found : heap[address]? = some (.list (checked.map text))) :
    Mutable.Relocation.emptyTupleAddress
      (heap.set address (.list ((checked ++ [s]).map text))) =
      Mutable.Relocation.emptyTupleAddress heap :=
  Mutable.Relocation.emptyTupleAddress_set _ _ _ _ found (by simp) (by simp)

/-- Appending a validated string preserves every relocated caller object. -/
theorem iterator_accepted_layout (logical heap : Mutable.Heap) (rename : Nat → Nat)
    (address : Nat) (checked : List String) (s : String)
    (layout : Mutable.Relocation.HeapLayout logical heap rename)
    (separate : ∀ index < logical.length, address ≠ rename index) :
    Mutable.Relocation.HeapLayout logical
      (heap.set address (.list ((checked ++ [s]).map text))) rename := by
  apply layout.preserves
  intro index inside
  exact iterator_accepted_preserves heap address (rename index) checked s (separate index inside)

/-- Actual iterator execution followed by validation preserves its relocated caller graph. -/
theorem iterator_accepted_attempt_layout (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (logical : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.HeapLayout logical yielded rename)
    (separate : ∀ index < logical.length, address ≠ rename index)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.HeapLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename ∧
      Mutable.Relocation.emptyTupleAddress
        (yielded.set address (.list ((checked ++ [s]).map text))) =
        Mutable.Relocation.emptyTupleAddress yielded := by
  obtain ⟨finalUsed, run⟩ := iterator_accepted_attempt context extension choices anchors used
    before yielded iterator operation address checked env s length digits isObject bound executed
    found getChecked following stack resumes
  exact ⟨finalUsed, run, iterator_accepted_layout logical yielded rename address checked s
    layout separate, iterator_accepted_emptyTuple yielded address checked s found⟩

/-- Appending a validated string retains the exact runtime objects used by the iterator. -/
theorem iterator_accepted_runtime (logical heap : Mutable.Heap) (rename : Nat → Nat)
    (address : Nat) (checked : List String) (s : String)
    (layout : Mutable.Relocation.RuntimeLayout logical heap rename)
    (separate : ∀ index < logical.length, address ≠ rename index) :
    Mutable.Relocation.RuntimeLayout logical
      (heap.set address (.list ((checked ++ [s]).map text))) rename := by
  apply layout.preserves
  intro index inside
  exact iterator_accepted_preserves heap address (rename index) checked s (separate index inside)

/-- Actual iterator execution followed by validation retains the complete runtime layout. -/
theorem iterator_accepted_attempt_runtime (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (logical : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.RuntimeLayout logical yielded rename)
    (separate : ∀ index < logical.length, address ≠ rename index)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.RuntimeLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename ∧
      Mutable.Relocation.emptyTupleAddress
        (yielded.set address (.list ((checked ++ [s]).map text))) =
        Mutable.Relocation.emptyTupleAddress yielded := by
  obtain ⟨finalUsed, run⟩ := iterator_accepted_attempt context extension choices anchors used
    before yielded iterator operation address checked env s length digits isObject bound executed
    found getChecked following stack resumes
  exact ⟨finalUsed, run, iterator_accepted_runtime logical yielded rename address checked s
    layout separate, iterator_accepted_emptyTuple yielded address checked s found⟩

/-- Reference validation preserves the invariants needed to execute the next iterator method. -/
theorem iterator_accepted_attempt_execution (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (logical : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.ExecutionLayout logical yielded rename)
    (separate : ∀ index < logical.length, address ≠ rename index)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.ExecutionLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename ∧
      Mutable.Relocation.emptyTupleAddress
        (yielded.set address (.list ((checked ++ [s]).map text))) =
        Mutable.Relocation.emptyTupleAddress yielded := by
  obtain ⟨finalUsed, run, related, interned⟩ := iterator_accepted_attempt_runtime
    context extension choices anchors used before yielded iterator operation address checked env s
    length digits isObject bound executed found getChecked logical rename layout.runtime separate
    following stack resumes
  exact ⟨finalUsed, run, layout.preserves related interned, interned⟩

/-- Validation updates the protected list and retains separation for the next caller method. -/
theorem iterator_accepted_attempt_private (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded logical : Mutable.Heap)
    (rename : Nat → Nat) (iterator : Mutable.Value) (operation : Operation)
    (address : Nat) (checked : List String) (env : HeapCalls.Env) (s : String)
    (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before = some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation before (.ok (text s)) yielded)
    (protectedLayout : Mutable.Relocation.PrivateLayout logical yielded rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env, stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
        (setLocal env "attempt" (text s)), stack,
        yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.PrivateLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename address (.list ((checked ++ [s]).map text)) := by
  obtain ⟨finalUsed, run⟩ := iterator_accepted_attempt context extension choices anchors used before yielded
    iterator operation address checked env s length digits isObject bound executed protectedLayout.saved getChecked following stack resumes
  exact ⟨finalUsed, run, protectedLayout.update_private _ (by simp) (by simp)⟩

theorem iterator_rejected_attempt (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (env : HeapCalls.Env) (s : String)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.completed (.ok ⟨.error (invalidException s), [], yielded, anchors⟩) finalUsed resumes) := by
  obtain ⟨middleUsed, advanced⟩ := IteratorCalls.advance_returns
    (loop := validationIteratorLoop env following stack) (anchors := anchors) (used := used)
    (resumes := resumes) isObject bound executed
  have rejected := rejected_attempt (setLocal env "attempt" (text s)) yielded s
    (by simp [setLocal]) invalid (validationLoop (sequenceSource iterator) 0 :: following)
      anchors stack
  obtain ⟨finalUsed, failed⟩ := IteratorCalls.completion_of_set
    (SetCalls.finishes_of_heap (finishes_extend rejected extension) choices middleUsed)
    (by intro completion same; cases same; simp [invalidException]) resumes
  refine ⟨finalUsed, advanced.trans ?_⟩
  simpa only [IteratorCalls.loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using failed


/-- The source for statement evaluates and acquires its input exactly once. -/
theorem iterator_enter (context : Module) (choices : ChoiceSchedule) (anchors used : Nat)
    (before after : Mutable.Heap) (receiver iterator : Mutable.Value)
    (operation advance : Operation) (env : HeapCalls.Env)
    (getInput : env "attempts" = some receiver)
    (isObject : IteratorCalls.isInstance before receiver = true)
    (bound : ProtocolCalls.iterMethod context receiver before = some (.ok operation, before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok iterator) after)
    (valid : ProtocolCalls.nextMethod context iterator after = some (.ok (some advance), after))
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (.forIn (.name "attempt") (.name "attempts") validationBody [] ::
        following) env, stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, after⟩, finalUsed⟩ resumes) :=
  IteratorCalls.for_instance (loop := validationIteratorLoop env following stack)
    (by intro expressions impossible; cases impossible)
    (Evaluates.lookup getInput) isObject bound executed valid

/-- Non-exhaustion failures escape before validation or updates to the graph or checked list. -/
theorem iterator_failed (context : Module) (choices : ChoiceSchedule) (anchors used : Nat)
    (before after : Mutable.Heap) (iterator : Mutable.Value) (operation : Operation)
    (env : HeapCalls.Env) (error : ExceptionObject)
    (notExhausted : error.typeName ≠ "StopIteration")
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.error error) after)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.completed (.ok ⟨.error error, [], after, anchors⟩) finalUsed resumes) :=
  IteratorCalls.advance_failed (loop := validationIteratorLoop env following stack)
    isObject bound executed notExhausted

theorem iterator_exhausted (context : Module) (choices : ChoiceSchedule) (anchors used : Nat)
    (before after : Mutable.Heap) (iterator : Mutable.Value) (operation : Operation)
    (env : HeapCalls.Env) (args : List Constant)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation before
      (.error ⟨"StopIteration", args⟩) after)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block following env, stack, after⟩, finalUsed⟩ resumes) :=
  IteratorCalls.advance_exhausted (loop := validationIteratorLoop env following stack)
    isObject bound executed

/-- One logical advancement supplies the reference consumer's actual call and yielded string. -/
theorem iterator_next_relocated (context : Module)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (anchors used : Nat) (logical physical after : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.ExecutionLayout logical physical rename)
    (iterator : Mutable.Value) (inside : iterator.edge.Within logical.length) (operation : Operation)
    (isObject : IteratorCalls.isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator logical = some (.ok (some operation), logical))
    (s : String) (executed : IteratorCalls.OperationCompletes context choices used operation logical (.ok (text s)) after)
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ other nextMap finalUsed,
      IteratorCalls.Relocation.ExtendedLayout logical.length physical.length rename after other nextMap ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
          stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationBody ++
          [Calls.loopContinuation validationBody
            (validationLoop (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0)] ++ following)
          (setLocal env "attempt" (text s)), stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, logicalRun⟩ := executed logical.length []
  obtain ⟨other, nextMap, extended, called⟩ := IteratorCalls.Relocation.advance_completion_relocates context choices
    logical physical rename logical.length anchors used finalUsed iterator operation (.ok (text s)) after []
    source layout inside (by simp [HeapCalls.Relocation.GlobalsWithin]) isObject bound logicalRun
  refine ⟨other, nextMap, finalUsed, extended, ?_⟩
  have calledRun := called (validationIteratorLoop env following stack) resumes
  have completion : IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop
        (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
        stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.ok (text s), [], other, anchors⟩) finalUsed
        (.advance (validationIteratorLoop env following stack) (Mutable.Relocation.relocateValue rename iterator) :: resumes)) := by
    simpa only [HeapCalls.Relocation.relocateGlobals, List.map_nil, Except.map,
      text, Mutable.Relocation.relocateValue] using calledRun
  exact IteratorCalls.advanced completion

/-- Exhaustion transports its final mutations before the reference loop exits. -/
theorem iterator_exhausted_relocated (context : Module)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (anchors used : Nat) (logical physical after : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.ExecutionLayout logical physical rename)
    (iterator : Mutable.Value) (inside : iterator.edge.Within logical.length) (operation : Operation)
    (isObject : IteratorCalls.isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator logical = some (.ok (some operation), logical))
    (args : List Constant) (executed : IteratorCalls.OperationCompletes context choices used operation logical
      (.error ⟨"StopIteration", args⟩) after)
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ other nextMap finalUsed,
      IteratorCalls.Relocation.ExtendedLayout logical.length physical.length rename after other nextMap ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
          stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block following env, stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, logicalRun⟩ := executed logical.length []
  obtain ⟨other, nextMap, extended, called⟩ := IteratorCalls.Relocation.advance_completion_relocates context choices
    logical physical rename logical.length anchors used finalUsed iterator operation (.error ⟨"StopIteration", args⟩) after []
    source layout inside (by simp [HeapCalls.Relocation.GlobalsWithin]) isObject bound logicalRun
  refine ⟨other, nextMap, finalUsed, extended, ?_⟩
  have completion : IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop
        (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
        stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.error ⟨"StopIteration", args⟩, [], other, anchors⟩) finalUsed
        (.advance (validationIteratorLoop env following stack) (Mutable.Relocation.relocateValue rename iterator) :: resumes)) := by
    simpa only [HeapCalls.Relocation.relocateGlobals, List.map_nil, Except.map] using
      called (validationIteratorLoop env following stack) resumes
  exact IteratorCalls.exhausted completion

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! A logical next-method execution supplies validation and preservation of the private checked list. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation
set_option Elab.async false

/-- No physical method execution or post-method private-list invariant is assumed. -/
theorem iterator_accepted_from_logical (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule) (anchors used finalUsed : Nat)
    (logical physical yielded : Mutable.Heap) (rename : Nat → Nat)
    (iterator : Mutable.Value) (operation : Operation) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (inside : iterator.edge.Within logical.length)
    (isObject : IteratorCalls.isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator logical = some (.ok (some operation), logical))
    (executed : IteratorCalls.Reaches context logical.length choices []
      (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (.completed (.ok ⟨.ok (text s), [], yielded, logical.length⟩) finalUsed []))
    (noGrowth : yielded.length = logical.length)
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List IteratorCalls.Resume) :
    ∃ (other : Mutable.Heap) (nextMap : Nat → Nat),
      (∀ index < logical.length, nextMap index = rename index) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (relocateValue rename iterator)) 0 :: following) env, stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (relocateValue rename iterator)) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          other.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      PrivateLayout yielded (other.set address (.list ((checked ++ [s]).map text))) nextMap
        address (.list ((checked ++ [s]).map text)) := by
  obtain ⟨other, nextMap, extended, kept, called⟩ := IteratorCalls.Relocation.advance_completion_isolated
    context choices logical physical rename logical.length anchors used finalUsed iterator operation (.ok (text s))
    yielded [] source layout.layout inside (by simp [HeapCalls.Relocation.GlobalsWithin]) isObject bound executed noGrowth
  have retainedList := kept address (.list (checked.map text)) layout
  have completion : IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following) env,
        stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.ok (text s), [], other, anchors⟩) finalUsed
        (.advance (validationIteratorLoop env following stack) (relocateValue rename iterator) :: resumes)) := by
    simpa only [HeapCalls.Relocation.relocateGlobals, List.map_nil, Except.map, text, relocateValue] using
      called (validationIteratorLoop env following stack) resumes
  have body := accepted_attempt_at other address checked (setLocal env "attempt" (text s)) s
    retainedList.saved (by simpa [setLocal] using getChecked) (by simp [setLocal]) length digits
  refine ⟨other, nextMap, extended.agrees, ?_, retainedList.update_private _ (by simp) (by simp)⟩
  apply (IteratorCalls.advanced completion).trans
  have resumed := IteratorCalls.Reaches.of_heap (choices := choices) (used := finalUsed)
    ((body.extend extension) (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
      anchors stack) resumes
  simpa only [IteratorCalls.loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using resumed

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Validation consumes a finite valid prefix and rejects the next invalid yield without reading further. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem validated_iterator_prefix (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical finalLogical : Mutable.Heap) (used finalUsed : Nat) (attempts : List String)
    (trace : YieldPrefix context choices iterator text logical used attempts finalLogical finalUsed)
    (noGrowth : finalLogical.length = logical.length)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after finalEnv,
      PrivateLayout finalLogical after rename address (.list ((checked ++ attempts).map text)) ∧
      finalEnv "checked" = some (.ref address) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          finalEnv, stack, after⟩, finalUsed⟩ resumes) := by
  induction trace generalizing physical checked env with
  | nil => exact ⟨physical, env, by simpa only [List.append_nil] using layout, getChecked, .refl⟩
  | @cons before middle after used nextUsed finalUsed s rest ran later ih =>
      obtain ⟨middleClosed, firstGrows⟩ := ran.effects source layout.layout.closed
      have laterGrows := (later.effects source middleClosed).2
      have firstSize : middle.length = before.length := by omega
      have laterSize : after.length = middle.length := by omega
      obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
      have accepted := valid s (by simp)
      obtain ⟨yieldedPhysical, nextMap, agrees, iteration, nextPrivate⟩ :=
        iterator_accepted_from_logical context extension source choices anchors used nextUsed before physical middle
          rename iterator operation address checked env s accepted.1 accepted.2 layout inside isObject bound
          executed firstSize getChecked following stack resumes
      have fixedMap : PrivateLayout middle
          (yieldedPhysical.set address (.list ((checked ++ [s]).map text))) rename
          address (.list ((checked ++ [s]).map text)) :=
        nextPrivate.congr (fun index bounded => (agrees index (by omega)).symm)
      obtain ⟨result, finalEnv, retained, finalChecked, continued⟩ := ih laterSize
        (fun value member => valid value (List.mem_cons_of_mem _ member))
        _ (checked ++ [s]) (setLocal env "attempt" (text s)) fixedMap
        (by simpa [setLocal] using getChecked)
      refine ⟨result, finalEnv, ?_, finalChecked, iteration.trans continued⟩
      simpa only [List.append_assoc, List.singleton_append] using retained

theorem iterator_rejected_from_logical (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical yielded physical : Mutable.Heap) (used finalUsed anchors : Nat)
    (s : String) (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (ran : NextRun context choices iterator logical used (.ok (text s)) yielded finalUsed)
    (noGrowth : yielded.length = logical.length) (rename : Nat → Nat)
    (address : Nat) (checked : List String)
    (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after, PrivateLayout yielded after rename address (.list (checked.map text)) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨.error (invalidException s), [], after, anchors⟩) finalUsed resumes) := by
  obtain ⟨after, _, kept, advanced⟩ := ran.scalar_isolated source physical rename layout.layout noGrowth anchors
  have rejected := rejected_attempt (setLocal env "attempt" (text s)) after s (by simp [setLocal]) invalid
    (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following) anchors stack
  have failed := completion_of_heap (choices := choices) (used := finalUsed) (finishes_extend rejected extension)
    (by intro completion same; cases same; simp [invalidException]) resumes
  refine ⟨after, kept address _ layout, (advanced (validationIteratorLoop env following stack) resumes).trans ?_⟩
  simpa only [loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using failed

theorem reject_after_iterator_prefix (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical middle yielded : Mutable.Heap) (used nextUsed finalUsed : Nat)
    (attempts : List String) (s : String)
    (trace : YieldPrefix context choices iterator text logical used attempts middle nextUsed)
    (ran : NextRun context choices iterator middle nextUsed (.ok (text s)) yielded finalUsed)
    (noGrowth : yielded.length = logical.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after, PrivateLayout yielded after rename address (.list ((checked ++ attempts).map text)) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨.error (invalidException s), [], after, anchors⟩) finalUsed resumes) := by
  obtain ⟨middleClosed, prefixGrows⟩ := trace.effects source layout.layout.closed
  have lastGrows := (ran.effects source middleClosed).2
  obtain ⟨middlePhysical, nextEnv, nextPrivate, _, accepted⟩ :=
    validated_iterator_prefix context extension source choices iterator logical middle used nextUsed attempts
      trace (by omega) valid physical rename address checked env layout getChecked following anchors stack resumes
  obtain ⟨after, finalPrivate, failed⟩ := iterator_rejected_from_logical context extension source choices
    iterator middle yielded middlePhysical nextUsed finalUsed anchors s invalid ran (by omega) rename
      address (checked ++ attempts) nextPrivate nextEnv following stack resumes
  exact ⟨after, finalPrivate, accepted.trans failed⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Reference validation composes every valid yielded attempt and the final iterator exit. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem validated_iterator_traversal (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical finalLogical : Mutable.Heap) (used finalUsed : Nat)
    (attempts : List String) (outcome : Except ExceptionObject Unit)
    (trace : Traversal context choices iterator text logical used attempts outcome finalLogical finalUsed)
    (noGrowth : finalLogical.length = logical.length)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after finalEnv,
      PrivateLayout finalLogical after rename address (.list ((checked ++ attempts).map text)) ∧
      finalEnv "checked" = some (.ref address) ∧
      ExitResult context choices anchors
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (validationIteratorLoop finalEnv following stack) resumes after finalUsed outcome := by
  obtain ⟨middle, nextUsed, error, first, last, result⟩ := trace.decompose
  obtain ⟨middleClosed, prefixGrows⟩ := first.effects source layout.layout.closed
  have lastGrows := (last.effects source middleClosed).2
  obtain ⟨middlePhysical, nextEnv, nextPrivate, nextChecked, accepted⟩ :=
    validated_iterator_prefix context extension source choices iterator logical middle used nextUsed attempts
      first (by omega) valid physical rename address checked env layout getChecked following anchors stack resumes
  obtain ⟨after, _, kept, exited⟩ := last.exit_isolated source middlePhysical rename nextPrivate.layout (by omega) anchors
  refine ⟨after, nextEnv, kept address _ nextPrivate, nextChecked, ?_⟩
  rw [← result]
  exact (exited (validationIteratorLoop nextEnv following stack) resumes).before accepted

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! The reference call allocates its checked list, acquires the iterator and retains acquisition effects. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

def iteratorEntryEnv (base : Mutable.Heap) (receiver : Mutable.Value) : HeapCalls.Env :=
  setLocal (functionEnv naiveArgs naiveBody [receiver] []) "checked" (.ref base.length)

theorem naive_iterator_initialize (base : Mutable.Heap) (receiver : Mutable.Value) (anchors : Nat)
    (stack : List HeapCalls.Frame) :
    HeapCalls.Reaches program anchors ⟨.operation (.call "naive") [receiver], stack, base⟩
      ⟨.block [.forIn (.name "attempt") (.name "attempts") validationBody [], .return checkedExpression]
        (iteratorEntryEnv base receiver), stack, base ++ [.list []]⟩ := by
  apply HeapCalls.Reaches.next (following :=
    ⟨.block naiveCode (functionEnv naiveArgs naiveBody [receiver] []), stack, base⟩) rfl
  have allocated : BlockContinues program (functionEnv naiveArgs naiveBody [receiver] [])
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str")) (some (.list []))]
      base (iteratorEntryEnv base receiver) (base ++ [.list []]) :=
    BlockContinues.annAssign (Evaluates.list .nil)
  simpa only [naive_source] using allocated
    [.forIn (.name "attempt") (.name "attempts") validationBody [], .return checkedExpression] anchors stack

theorem naive_iterator_entry (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired : Mutable.Heap) (used finalUsed anchors : Nat)
    (closed : Closed base) (ran : AcquireRun context choices receiver base used iterator acquired finalUsed)
    (noGrowth : acquired.length = base.length) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after, PrivateLayout acquired after id base.length (.list []) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.operation (.call "naive") [receiver], stack, base⟩, used⟩ resumes)
        (.running ⟨⟨.block [validationLoop (sequenceSource iterator) 0, .return checkedExpression]
          (iteratorEntryEnv base receiver), stack, after⟩, finalUsed⟩ resumes) := by
  have layout := (ExecutionLayout.refl base closed).new_private_cell (.list []) (by simp)
  obtain ⟨after, _, kept, entered⟩ := ran.for_name_isolated source (base ++ [.list []]) id layout.layout noGrowth anchors
  refine ⟨after, kept base.length _ layout, ?_⟩
  apply (IteratorCalls.Reaches.of_heap ((naive_iterator_initialize base receiver anchors stack).extend extension) resumes).trans
  simpa only [relocateValue_id, loopCode, validationIteratorLoop] using entered
    (validationIteratorLoop (iteratorEntryEnv base receiver) [.return checkedExpression] stack) resumes "attempts"
    (by simpa only [relocateValue_id] using
      (show iteratorEntryEnv base receiver "attempts" = some receiver from rfl))

theorem naive_iterator_rejection (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle yielded : Mutable.Heap)
    (acquiredUsed nextUsed finalUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String) (s : String)
    (trace : YieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (ran : NextRun context choices iterator middle nextUsed (.ok (text s)) yielded finalUsed)
    (noGrowth : yielded.length = base.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) :
    ∃ after, PrivateLayout yielded after id base.length (.list (attempts.map text)) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error (invalidException s), [], after, base.length⟩ := by
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.effects source closed
  obtain ⟨middleClosed, prefixGrows⟩ := trace.effects source acquiredClosed
  have lastGrows := (ran.effects source middleClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition (by omega) [] []
  obtain ⟨after, finalPrivate, failed⟩ := reject_after_iterator_prefix context extension source choices iterator
    acquired middle yielded acquiredUsed nextUsed finalUsed attempts s trace ran (by omega) valid invalid
      initialized id base.length [] (iteratorEntryEnv base receiver) layout
      (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  refine ⟨after, by simpa only [List.nil_append] using finalPrivate, ?_⟩
  exact (entered.trans (by simpa only [relocateValue_id] using failed)).finishes (.done rfl)

theorem naive_iterator_failure (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired yielded : Mutable.Heap)
    (acquiredUsed finalUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String) (error : ExceptionObject)
    (trace : Traversal context choices iterator text acquired acquiredUsed attempts (.error error) yielded finalUsed)
    (noGrowth : yielded.length = base.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true) :
    ∃ after, PrivateLayout yielded after id base.length (.list (attempts.map text)) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error error, [], after, base.length⟩ := by
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.effects source closed
  have traversalGrows := (trace.effects source acquiredClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition (by omega) [] []
  obtain ⟨after, _, finalPrivate, _, failed⟩ := validated_iterator_traversal context extension source choices iterator
    acquired yielded acquiredUsed finalUsed attempts (.error error) trace (by omega) valid
      initialized id base.length [] (iteratorEntryEnv base receiver) layout
      (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  refine ⟨after, by simpa only [List.nil_append] using finalPrivate, ?_⟩
  exact (entered.trans (by simpa only [ExitResult, relocateValue_id] using failed)).finishes (.done rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p79

/-! Validation follows the schedule through every finite set, including mixed valid and invalid attempts. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def setValidationLoop (address : Nat) (original remaining : List String) : Stmt :=
  .setStepLoop "attempt" address (original.map Constant.string) (remaining.map Constant.string)
    validationBody []

theorem validated_set (choices : ChoiceSchedule) (used : Nat) (base : Mutable.Heap)
    (address : Nat) (original remaining checked : List String) (env : HeapCalls.Env)
    (found : base[address]? = some (.set (original.map Constant.string)))
    (getChecked : env "checked" = some (.ref base.length)) (anchors : Nat) :
    ∃ after, Finishes (SetCalls.step program anchors choices)
      ⟨⟨.block [setValidationLoop address original remaining, .return checkedExpression] env,
        [], base ++ [.list (checked.map text)]⟩, used⟩
      (.ok ⟨validatedOutcome checked (SetCalls.selectionOrder choices used remaining), [], after, anchors⟩) ∧
      base <+: after := by
  have retained : (base ++ [.list (checked.map text)])[address]? =
      some (.set (original.map Constant.string)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  cases remaining with
  | nil =>
      obtain ⟨after, returned, saved⟩ := checked_return_result
        (base ++ [.list (checked.map text)]) base.length checked (by simp) env getChecked
      refine ⟨after, ?_, (List.prefix_append _ _).trans saved⟩
      simp only [SetCalls.selectionOrder, validatedOutcome]
      apply Finishes.next (following :=
        ⟨⟨.block [.return checkedExpression] env, [], base ++ [.list (checked.map text)]⟩, used⟩)
      · simp [SetCalls.step, step, SetCalls.iteratorStep, setValidationLoop, retained]
      · exact SetCalls.finishes_of_heap (SourceResult.finishes _ _ _ _ returned anchors) choices used
  | cons head tail =>
      let index := choices used % (head :: tail).length
      have bounded : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let s := (head :: tail)[index]
      let rest := (head :: tail).eraseIdx index
      let bound := setLocal env "attempt" (text s)
      have boundChecked : bound "checked" = some (.ref base.length) := by
        simpa [bound, setLocal] using getChecked
      have boundAttempt : bound "attempt" = some (text s) := by simp [bound, setLocal]
      have selected : ((head :: tail).map Constant.string)[index]? = some (.string s) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem bounded]
        rfl
      have control : Calls.loopControl validationBody = false := rfl
      have entered : SetCalls.step program anchors choices
          ⟨⟨.block [setValidationLoop address original (head :: tail), .return checkedExpression] env,
            [], base ++ [.list (checked.map text)]⟩, used⟩ =
          .next ⟨⟨.block (validationBody ++ [setValidationLoop address original rest,
            .return checkedExpression]) bound, [], base ++ [.list (checked.map text)]⟩, used + 1⟩ := by
        simpa only [setValidationLoop, Calls.loopContinuation, control, Bool.false_eq_true,
          ↓reduceIte, List.eraseIdx_map, List.singleton_append, rest, bound, text] using
          SetCalls.select_item_mod program choices anchors used address index
            (base ++ [.list (checked.map text)]) (original.map Constant.string)
            ((head :: tail).map Constant.string) (.string s) env "attempt" validationBody []
            [.return checkedExpression] [] retained selected (by simp [index])
      rw [SetCalls.selectionOrder]
      change ∃ after, Finishes (SetCalls.step program anchors choices)
        ⟨⟨.block [setValidationLoop address original (head :: tail), .return checkedExpression] env,
          [], base ++ [.list (checked.map text)]⟩, used⟩
        (.ok ⟨validatedOutcome checked (s :: SetCalls.selectionOrder choices (used + 1) rest),
          [], after, anchors⟩) ∧ base <+: after
      by_cases valid : s.length = 3 ∧ Strings.isDigit s = true
      · simp only [validatedOutcome, if_pos valid]
        obtain ⟨after, completed, saved⟩ := validated_set choices (used + 1) base address original rest
          (checked ++ [s]) bound found boundChecked anchors
        refine ⟨after, .next entered ?_, saved⟩
        exact (SetCalls.Reaches.of_heap
          (accepted_attempt base checked bound s boundChecked boundAttempt valid.1 valid.2
            [setValidationLoop address original rest, .return checkedExpression] anchors [])
          choices (used + 1)).finishes completed
      · simp only [validatedOutcome, if_neg valid]
        refine ⟨base ++ [.list (checked.map text)], .next entered ?_, List.prefix_append _ _⟩
        apply SetCalls.finishes_of_heap (rejected_attempt bound _ s boundAttempt ?_ _ anchors [])
        by_cases length : s.length = 3
        · exact Or.inr (by simpa [length] using valid)
        · exact Or.inl length
termination_by remaining.length
decreasing_by
  rw [List.length_eraseIdx_of_lt bounded]
  simp

theorem naive_set_finishes (choices : ChoiceSchedule) (base : Mutable.Heap)
    (address : Nat) (attempts : List String)
    (found : base[address]? = some (.set (attempts.map Constant.string))) :
    ∃ after, ((SetCalls.call program "naive" [.ref address] base).run choices).Finishes
      ⟨validatedOutcome [] (SetCalls.selectionOrder choices 0 attempts), [], after, base.length⟩ ∧
      base <+: after := by
  let env := setValidationEnv (.ref address)
  let bound := setLocal env "checked" (.ref base.length)
  let heap := base ++ [Mutable.Object.list []]
  obtain ⟨after, completed, saved⟩ := validated_set choices 0 base address attempts attempts []
    bound found (by simp [bound, setLocal]) base.length
  refine ⟨after, ?_, saved⟩
  change Finishes (SetCalls.step program base.length choices)
    ⟨⟨.operation (.call "naive") [.ref address], [], base⟩, 0⟩ _
  apply (SetCalls.Reaches.of_heap
    (show HeapCalls.Reaches program base.length
      ⟨.operation (.call "naive") [.ref address], [], base⟩ ⟨.block naiveCode env, [], base⟩
      from .next rfl .refl) choices 0).finishes
  rw [naive_source]
  have allocated : BlockContinues program env
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str")) (some (.list []))]
      base bound heap := BlockContinues.annAssign (Evaluates.list .nil)
  apply (SetCalls.Reaches.of_heap (allocated _ base.length []) choices 0).finishes
  apply (SetCalls.for_set_name program choices base.length 0 address heap
    (attempts.map Constant.string) bound "attempt" "attempts" validationBody []
    [.return checkedExpression] [] (by rfl) ?_).finishes completed
  simpa only [heap, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found

/-- Reordering validated attempts changes neither their graph constraints nor the least ordering. -/
theorem checkedOutcome_perm (left right : List String) (permutation : left.Perm right) :
    checkedOutcome left = checkedOutcome right := by
  have characters : (attemptCharacters left).Perm (attemptCharacters right) :=
    permutation.flatMap_right (fun (s : String) => s.toList.map String.singleton)
  have nodes : (nodeValues left).Perm (nodeValues right) := by
    apply (List.perm_ext_iff_of_nodup (node_values_unique left) (node_values_unique right)).mpr
    intro value
    have contents (attempts : List String) : value ∈ nodeValues attempts ↔ value ∈ attemptCharacters attempts := by
      simpa [nodeValues] using dedupBy_keys id [] (attemptCharacters attempts) value
    exact (contents left).trans (characters.mem_iff.trans (contents right).symm)
  have edges : (attemptEdges left).Perm (attemptEdges right) :=
    permutation.flatMap_right observationPairs
  unfold checkedOutcome
  rw [ProjectEulerStatements.TopologicalOrder.order_nodes_perm _ _ _ nodes,
    ProjectEulerStatements.TopologicalOrder.order_edges_congr _ _ _ (fun _ => edges.mem_iff)]

end data.«project-euler-statements».data.py.project_euler_statements.p79
