import data.«project-euler-statements».data.py.project_euler_statements.«p87.py.lean.d».Inputs
import ProjectEulerSolutions.Lib.PrimePowerTriplesSearch

namespace data.«project-euler-statements».data.py.project_euler_statements.p87.naive
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def natValues (items : List Nat) : List Mutable.Value := items.map (fun (n : Nat) => number n)
def working (base : Mutable.Heap) (items : List Nat) : Mutable.Heap := base ++ [.list (natValues items)]

theorem working_found (base : Mutable.Heap) (items : List Nat) :
    (working base items)[base.length]? = some (.list (natValues items)) := by simp [working]

theorem working_store (base : Mutable.Heap) (items replacement : List Nat) :
    (working base items).set base.length (.list (natValues replacement)) = working base replacement := by
  simp [working, List.set_append_right]

theorem input_sequence (base : Mutable.Heap) (address : Nat) (items sums : List Nat)
    (found : base[address]? = some (.list (natValues items))) :
    Mutable.sequence (.ref address) (working base sums) =
      some (.ok (natValues items), working base sums) := by
  simp [working, Mutable.sequence, ProjectEulerSolutions.HeapCollection.prefix_found base _ address _ found]

/-- Each nested source loop traverses the unchanged prime list and appends to a distinct collector. -/
theorem collect_sequence (name : String) (body : List Stmt) (control : Calls.loopControl body = false)
    (items : List Nat) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (natValues items)))
    (emits : Nat → List Nat) (Ready : HeapCalls.Env → Prop)
    (bindReady : ∀ env, Ready env → ∀ (value : Nat), Ready (setLocal env name (number value)))
    (step : ∀ (value : Nat) sums env, Ready env → env name = some (number value) →
      ∃ finalEnv, BlockContinues program env body (working base sums) finalEnv
        (working base (sums ++ emits value)) ∧ Ready finalEnv)
    (remaining : List Nat) (position : Nat) (suffix : items.drop position = remaining)
    (sums : List Nat) (env : HeapCalls.Env) (ready : Ready env) :
    ∃ finalEnv, BlockContinues program env [.sequenceStepLoop name (.ref address) position body []]
      (working base sums) finalEnv (working base (sums ++ remaining.flatMap emits)) ∧ Ready finalEnv := by
  induction remaining generalizing position sums env with
  | nil =>
      refine ⟨env, ?_, ready⟩
      simp only [List.flatMap_nil, List.append_nil]
      apply BlockContinues.sequence_done (source := .ref address) (heap := working base sums) (items := natValues items)
        (input_sequence base address items sums found)
      · have missing : items[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        simp only [natValues, List.getElem?_map, missing, Option.map_none]
      · exact .nil
  | cons head tail ih =>
      let bound := setLocal env name (number head)
      obtain ⟨nextEnv, executed, nextReady⟩ := step head sums bound
        (bindReady env ready head) (by simp [bound, setLocal])
      obtain ⟨finalEnv, continued, finalReady⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (sums ++ emits head) nextEnv nextReady
      refine ⟨finalEnv, ?_, finalReady⟩
      have selected : items[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      apply BlockContinues.sequence_step (source := .ref address) (items := natValues items) (value := number head)
        (input_sequence base address items sums found) (by simp only [natValues, List.getElem?_map, selected, Option.map_some])
      simpa only [Calls.loopContinuation, control, Bool.false_eq_true, if_false,
        List.flatMap_cons, List.append_assoc] using executed.append continued

theorem collect_for (name : String) (body : List Stmt) (control : Calls.loopControl body = false)
    (items : List Nat) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (natValues items)))
    (emits : Nat → List Nat) (Ready : HeapCalls.Env → Prop)
    (bindReady : ∀ env, Ready env → ∀ (value : Nat), Ready (setLocal env name (number value)))
    (step : ∀ (value : Nat) sums env, Ready env → env name = some (number value) →
      ∃ finalEnv, BlockContinues program env body (working base sums) finalEnv
        (working base (sums ++ emits value)) ∧ Ready finalEnv)
    (sums : List Nat) (env : HeapCalls.Env) (ready : Ready env)
    (getPs : env "ps" = some (.ref address)) :
    ∃ finalEnv, BlockContinues program env [.forIn (.name name) (.name "ps") body []]
      (working base sums) finalEnv (working base (sums ++ items.flatMap emits)) ∧ Ready finalEnv := by
  obtain ⟨finalEnv, executed, finalReady⟩ := collect_sequence name body control items base address found
    emits Ready bindReady step items 0 rfl sums env ready
  refine ⟨finalEnv, ?_, finalReady⟩
  apply BlockContinues.for_sequence (value := .ref address) (items := natValues items)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getPs)
    (input_sequence base address items sums found)
  exact executed

end data.«project-euler-statements».data.py.project_euler_statements.p87.naive
