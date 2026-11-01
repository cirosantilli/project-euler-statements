import Mathlib.Data.Nat.Basic

/-! Deterministic searches with a least partial denotation and finite execution proofs. -/
namespace ProjectEulerStatements.UnboundedSearch
set_option Elab.async false

/-- A left step returns a result; a right step continues without an exhaustion bound. -/
def run {S A : Type} (step : S → Sum A S) (state : S) : Option A :=
  match step state with
  | .inl result => some result
  | .inr next => run step next
partial_fixpoint

inductive Finishes {S A : Type} (step : S → Sum A S) : S → A → Prop where
  | done {state : S} {result : A} : step state = .inl result → Finishes step state result
  | next {state following : S} {result : A} :
      step state = .inr following → Finishes step following result → Finishes step state result

theorem run_some_iff {S A : Type} (step : S → Sum A S) (state : S) (result : A) :
    run step state = some result ↔ Finishes step state result := by
  constructor
  · have sound : ∀ state result, run step state = some result → Finishes step state result := by
      apply run.fixpoint_induct step (motive := fun recur =>
        ∀ state result, recur state = some result → Finishes step state result)
      · exact Lean.Order.admissible_pi_apply _ (fun state =>
          Lean.Order.admissible_pi _ (fun result => Lean.Order.Option.admissible_eq_some _ result))
      · intro recur ih state result returned
        cases transition : step state with
        | inl value =>
            simp only [transition, Option.some.injEq] at returned
            subst result
            exact .done transition
        | inr next =>
            simp only [transition] at returned
            exact .next transition (ih next result returned)
    exact sound state result
  · intro finished
    induction finished with
    | done transition => rw [run.eq_1, transition]
    | next transition _ ih => rw [run.eq_1, transition]; exact ih

/-- A relation that preserves each return and continuation gives equal partial results. -/
theorem run_equiv {S T A : Type} (left : S → Sum A S) (right : T → Sum A T)
    (related : S → T → Prop)
    (simulation : ∀ s t, related s t →
      (∃ result, left s = .inl result ∧ right t = .inl result) ∨
      (∃ nextS nextT, left s = .inr nextS ∧ right t = .inr nextT ∧ related nextS nextT))
    (s : S) (t : T) (initial : related s t) : run left s = run right t := by
  have forward : ∀ s result, Finishes left s result →
      ∀ t, related s t → Finishes right t result := by
    intro s result finished
    induction finished with
    | @done s result terminal =>
        intro t holds
        rcases simulation s t holds with ⟨value, hit, other⟩ | ⟨_, _, miss, _, _⟩
        · have same : result = value := Sum.inl.inj (terminal.symm.trans hit)
          subst value
          exact .done other
        · rw [terminal] at miss
          contradiction
    | @next s next result transition rest ih =>
        intro t holds
        rcases simulation s t holds with ⟨_, hit, _⟩ | ⟨nextS, nextT, miss, other, nextRelated⟩
        · rw [transition] at hit
          contradiction
        · have same : next = nextS := Sum.inr.inj (transition.symm.trans miss)
          subst nextS
          exact .next other (ih nextT nextRelated)
  have backward : ∀ t result, Finishes right t result →
      ∀ s, related s t → Finishes left s result := by
    intro t result finished
    induction finished with
    | @done t result terminal =>
        intro s holds
        rcases simulation s t holds with ⟨value, other, hit⟩ | ⟨_, _, _, miss, _⟩
        · have same : result = value := Sum.inl.inj (terminal.symm.trans hit)
          subst value
          exact .done other
        · rw [terminal] at miss
          contradiction
    | @next t next result transition rest ih =>
        intro s holds
        rcases simulation s t holds with ⟨_, _, hit⟩ | ⟨nextS, nextT, other, miss, nextRelated⟩
        · rw [transition] at hit
          contradiction
        · have same : next = nextT := Sum.inr.inj (transition.symm.trans miss)
          subst nextT
          exact .next other (ih nextS nextRelated)
  cases found : run left s with
  | none =>
      cases other : run right t with
      | none => rfl
      | some value =>
          have finished := backward t value ((run_some_iff right t value).mp other) s initial
          have impossible := (run_some_iff left s value).mpr finished
          rw [found] at impossible
          contradiction
  | some value => exact ((run_some_iff right t value).mpr
      (forward s value ((run_some_iff left s value).mp found) t initial)).symm

end ProjectEulerStatements.UnboundedSearch
