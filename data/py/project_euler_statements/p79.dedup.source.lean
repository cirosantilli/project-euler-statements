import data.«project-euler-statements».data.py.project_euler_statements.«p79.membership.source»

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
