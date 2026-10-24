import ProjectEulerStatements.Lib.MagicRingTextCalls

/-! Numeric minimum identifies the canonical starting outer label. -/
namespace ProjectEulerStatements.MagicRingMinimumCalls
open FormalSW.PyAst HeapCalls MagicRing MagicRingTextCalls
set_option Elab.async false

theorem fold_min_le (values : List Nat) (best : Nat) : values.foldl min best ≤ best := by
  induction values generalizing best with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact (ih (min best first)).trans (min_le_left _ _)

theorem fold_min_le_member (values : List Nat) (best value : Nat) (member : value ∈ values) :
    values.foldl min best ≤ value := by
  induction values generalizing best with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact (fold_min_le rest (min best first)).trans (min_le_right _ _)
      · exact ih (min best first) later

theorem le_fold_min (values : List Nat) (best lower : Nat) (initial : lower ≤ best)
    (bounds : ∀ value ∈ values, lower ≤ value) : lower ≤ values.foldl min best := by
  induction values generalizing best with
  | nil => exact initial
  | cons first rest ih =>
      exact ih (min best first) (le_min initial (bounds first List.mem_cons_self))
        (fun value member => bounds value (List.mem_cons_of_mem _ member))

theorem fold_min_eq (values : List Nat) (best : Nat) :
    values.foldl min best = best ↔ ∀ value ∈ values, best ≤ value := by
  constructor
  · intro same value member
    rw [← same]
    exact fold_min_le_member values best value member
  · intro bounds
    exact le_antisymm (fold_min_le values best)
      (le_fold_min values best best (Nat.le_refl _) bounds)

theorem canonical_iff {n : Nat} (ring : Ring n) (first : Nat) (rest : List Nat)
    (outer : ring.outer = first :: rest) :
    Canonical ring ↔ first = rest.foldl min first := by
  simp only [Canonical, outer, List.headD_cons, List.mem_cons, forall_eq_or_imp, le_refl,
    true_and, eq_comm (a := first), fold_min_eq]

theorem minimumFrom_nats (values : List Nat) (best : Nat) :
    Calls.minimumFrom (.int best) (values.map (fun value : Nat => Constant.int value)) =
      .ok (.int (values.foldl min best : Nat)) := by
  induction values generalizing best with
  | nil => rfl
  | cons first rest ih =>
      by_cases smaller : first < best
      · simp [Calls.minimumFrom, scalarCompare, evalCmpOp, smaller, ih,
          min_eq_right (Nat.le_of_lt smaller)]
      · simp [Calls.minimumFrom, scalarCompare, evalCmpOp, smaller, ih,
          min_eq_left (Nat.le_of_not_gt smaller)]

theorem minimum_result (program : Module) (first : Nat) (rest : List Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (localOuter : env "outer" = some (.ref address))
    (getOuter : heap[address]? = some (.list (encode (first :: rest)))) :
    Evaluates program env (.builtinCall .min [.name "outer"])
      heap (number (rest.foldl min first)) heap := by
  apply Evaluates.builtin (.cons (Evaluates.lookup localOuter) .nil)
  have converted (values : List Nat) :
      ((encode values).mapM (fun item => match item with
        | .scalar value => pure value
        | .ref _ => Mutable.unsupported) : Mutable.Eval (List Constant)) =
      pure (values.map (fun value : Nat => Constant.int value)) := by
    simp only [encode, List.mapM_map]
    change (values.mapM (fun value : Nat => pure (Constant.int value)) :
      Mutable.Eval (List Constant)) = _
    exact List.mapM_pure
  have execution (items : List Mutable.Value) (present : heap[address]? = some (.list items)) :
      primitive (.builtin .min) [.ref address] heap =
        ((do
          let scalars ← items.mapM (fun item => match item with
            | .scalar value => pure value
            | .ref _ => Mutable.unsupported)
          scalarResult (some (ScalarSet.minimum scalars))) : Mutable.Eval Mutable.Value) heap := by
    simp [primitive, Mutable.sequence, present]
    rfl
  rw [execution _ getOuter, converted]
  change scalarResult (some (ScalarSet.minimum
    ((first :: rest).map (fun value : Nat => Constant.int value)))) heap = _
  rw [show ScalarSet.minimum ((first :: rest).map (fun value : Nat => Constant.int value)) =
    .ok (.int (rest.foldl min first : Nat)) from minimumFrom_nats rest first]
  rfl

theorem canonical_condition (program : Module) {n : Nat} (ring : Ring n) (positive : 0 < n)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (localOuter : env "outer" = some (.ref address))
    (getOuter : heap[address]? = some (.list (encode ring.outer))) :
    ∃ flag, Evaluates program env
      (.compare (.subscript (.name "outer") (.constant (.int 0)))
        [(.notEq, .builtinCall .min [.name "outer"])]) heap (.scalar (.bool flag)) heap ∧
      (flag = false ↔ Canonical ring) := by
  cases shape : ring.outer with
  | nil => have size := ring.outer_length; simp [shape] at size; omega
  | cons first rest =>
      refine ⟨decide (first ≠ rest.foldl min first), ?_, ?_⟩
      · apply Evaluates.compare (av := number first) (bv := number (rest.foldl min first))
          (middle := heap) (afterRight := heap)
        · exact index_evaluates program heap env "outer" address 0 false ring.outer first
            (.constant (.int 0)) localOuter Evaluates.constant
            (by intros a b c impossible; cases impossible) getOuter (by simp [shape])
        · exact minimum_result program first rest heap env address localOuter
            (by simpa only [shape] using getOuter)
        · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      · simp only [decide_eq_false_iff_not, ne_eq, not_not, canonical_iff ring first rest shape]

end ProjectEulerStatements.MagicRingMinimumCalls
