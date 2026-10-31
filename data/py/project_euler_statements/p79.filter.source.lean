import data.«project-euler-statements».data.py.project_euler_statements.«p79.edges.source»

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
