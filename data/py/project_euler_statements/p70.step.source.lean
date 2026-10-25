import data.«project-euler-statements».data.py.project_euler_statements.«p70.better.source»

/-! Heap allocations and strict record updates for one reference-search candidate. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst HeapCalls ProjectEulerStatements TotientPermutation
set_option Elab.async false

abbrev naiveArgs : List Arg := ((findFunctionIn program.body "naive").getD ([], [])).1
abbrev naiveBody : List Stmt := ((findFunctionIn program.body "naive").getD ([], [])).2
abbrev candidateCondition : Expr := .boolOp .and
  [.compare (.name "n") [(.gt, .constant (.int 1))],
    .call (.name "is_permutation") [.name "n", phiExpression "n"]]
abbrev updateCondition : Expr := .boolOp .or
  [.compare (.name "best") [(.eq, .constant (.int 0))],
    .call (.name "better") [.name "n", .name "best"]]
abbrev loopBody : List Stmt :=
  [.ifThen candidateCondition
    [.ifThen updateCondition [.assign [.name "best"] (.name "n")] []] []]

theorem naive_function_source : findFunctionIn program.body "naive" =
    some (naiveArgs, naiveBody) := rfl

theorem naive_code_source : executableBody naiveBody =
    [.assign [.name "best"] (.constant (.int 0)),
      .forIn (.name "n") (.call (.name "range")
        [.binOp (.name "limit") .add (.constant (.int 1))]) loopBody [],
      .return (.name "best")] := rfl

def candidateObjects (n : Nat) : Mutable.Heap :=
  if 1 < n then digitObjects n ++ digitObjects n.totient else []

theorem candidate_condition_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    Evaluates program env candidateCondition heap (flag (decide (eligible n)))
      (heap ++ candidateObjects n) := by
  have largeTest : Evaluates program env (.compare (.name "n") [(.gt, .constant (.int 1))])
      heap (flag (decide (1 < n))) heap := by
    exact Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup getN) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases large : 1 < n
  · have permutation : Evaluates program env
        (.call (.name "is_permutation") [.name "n", phiExpression "n"]) heap
        (flag (isPermutation n n.totient)) (heap ++ digitObjects n ++ digitObjects n.totient) :=
      Evaluates.call (.cons (Evaluates.lookup getN)
        (.cons (phi_expression_result "n" n heap env getN) .nil))
        (is_permutation.result n n.totient heap)
    have accepted : decide (eligible n) = isPermutation n n.totient := by
      cases chosen : isPermutation n n.totient <;> simp [eligible, large, chosen]
    rw [accepted]
    simp only [candidateObjects, if_pos large, ← List.append_assoc]
    apply Evaluates.boolean_next (by simpa only [large, decide_true] using largeTest) rfl rfl
    exact Evaluates.boolean_last permutation rfl
  · have absent : ¬ eligible n := fun chosen => large chosen.1
    simp only [candidateObjects, if_neg large, List.append_nil, absent, decide_false]
    exact Evaluates.boolean_stop (by simpa only [large, decide_false] using largeTest) rfl rfl

theorem update_condition_result (n best : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getBest : env "best" = some (number best)) :
    Evaluates program env updateCondition heap
      (flag (decide (best = 0 ∨ TotientPermutation.better n best = true))) heap := by
  have zeroTest : Evaluates program env (.compare (.name "best") [(.eq, .constant (.int 0))])
      heap (flag (decide (best = 0))) heap := by
    exact Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup getBest) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases zero : best = 0
  · simpa only [zero, true_or, decide_true] using
      (Evaluates.boolean_stop (op := .or)
        (rest := [.call (.name "better") [.name "n", .name "best"]])
        (by simpa only [zero, decide_true] using zeroTest) rfl rfl)
  · apply Evaluates.boolean_next (by simpa only [zero, decide_false] using zeroTest) rfl rfl
    have compared : Evaluates program env (.call (.name "better") [.name "n", .name "best"])
        heap (flag (TotientPermutation.better n best)) heap :=
      Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getBest) .nil))
        (better.result n best heap)
    simpa only [zero, false_or, Bool.decide_coe] using Evaluates.boolean_last compared rfl

/-- The reference keeps the first winner on ties, including all conditional allocations. -/
theorem candidate_step (n best : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getBest : env "best" = some (number best)) :
    ∃ finalEnv, BlockContinues program env loopBody heap finalEnv (heap ++ candidateObjects n) ∧
      finalEnv "best" = some (number (visit best n)) := by
  have tested := candidate_condition_result n heap env getN
  by_cases accepted : eligible n
  · have compared := update_condition_result n best (heap ++ candidateObjects n) env getN getBest
    by_cases improved : best = 0 ∨ TotientPermutation.better n best = true
    · refine ⟨setLocal env "best" (number n), ?_, ?_⟩
      · apply BlockContinues.branch (flag := true)
          (by simpa only [accepted, decide_true] using tested) rfl
        apply BlockContinues.branch (flag := true)
          (by simpa only [improved, decide_true] using compared) rfl
        exact BlockContinues.assign (Evaluates.lookup getN)
      · simp only [visit, if_pos accepted, if_pos improved, setLocal, if_true]
    · refine ⟨env, ?_, ?_⟩
      · apply BlockContinues.branch (flag := true)
          (by simpa only [accepted, decide_true] using tested) rfl
        apply BlockContinues.branch (flag := false)
          (by simpa only [improved, decide_false] using compared) rfl
        exact .nil
      · simpa only [visit, if_pos accepted, if_neg improved] using getBest
  · refine ⟨env, ?_, ?_⟩
    · apply BlockContinues.branch (flag := false)
        (by simpa only [accepted, decide_false] using tested) rfl
      exact .nil
    · simpa only [visit, if_neg accepted] using getBest

end data.«project-euler-statements».data.py.project_euler_statements.p70
