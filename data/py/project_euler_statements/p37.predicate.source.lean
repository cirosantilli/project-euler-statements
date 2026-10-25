import data.«project-euler-statements».data.py.project_euler_statements.«p37.truncations.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p37
open FormalSW.PyAst HeapCalls ProjectEulerStatements.TruncatablePrimeBase
private abbrev program := P37Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

private abbrev allExpr : Expr := .consumeGenerator (.builtinCall .all [])
  (.call (.name "is_prime") [.name "x"])
  [(.name "x", .call (.name "truncations") [.name "n", .name "base"], [])]

private theorem all_result (radix n : Nat) (valid : 2 ≤ radix) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (getN : env "n" = some (number n))
    (getBase : env "base" = some (number radix)) :
    ∃ extra, Evaluates program env allExpr heap (flag (digitCheck radix n)) (heap ++ extra) := by
  obtain ⟨extra, address, truncated, found⟩ := truncations.result radix n valid heap
  refine ⟨extra, ?_⟩
  apply Evaluates.all_map (values := truncations radix n) (encode := number)
    (predicate := fun item => decide (Nat.Prime item))
    (by intro expressions; simp) (by intro expressions; simp) (by intro expressions; simp)
    (Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getBase) .nil)) truncated)
    (by simp [Mutable.sequence, found])
  intro inner item selected
  exact Evaluates.call (.cons (Evaluates.lookup selected) .nil)
    ((common.is_prime.heap_result item (heap ++ extra)).extend common_extension)

/-- Both guards short-circuit before allocating any truncation lists. -/
theorem is_truncatable_prime.result (radix n : Nat) (valid : 2 ≤ radix) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "is_truncatable_prime" [number n, number radix] heap
      (flag (referenceCheck radix n)) (heap ++ extra) := by
  let args := ((findFunctionIn program.body "is_truncatable_prime").getD ([], [])).1
  let code := ((findFunctionIn program.body "is_truncatable_prime").getD ([], [])).2
  let env := functionEnv args code [number n, number radix] []
  have threshold : Evaluates program env (.compare (.name "n") [(.gtE, .name "base")]) heap
      (flag (decide (radix ≤ n))) heap :=
    Evaluates.compare (Evaluates.lookup rfl) (Evaluates.lookup rfl)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases small : n < radix
  · refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    simp only [referenceCheck, show ¬ radix ≤ n by omega, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop (flag := false)
      (by simpa only [show ¬ radix ≤ n by omega, decide_false] using threshold) rfl rfl
  · have primality : Evaluates program env (.call (.name "is_prime") [.name "n"]) heap
        (flag (decide (Nat.Prime n))) heap :=
      Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
        ((common.is_prime.heap_result n heap).extend common_extension)
    by_cases prime : Nat.Prime n
    · obtain ⟨extra, truncated⟩ := all_result radix n valid heap env rfl rfl
      refine ⟨extra, ?_⟩
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      simp only [referenceCheck, show radix ≤ n by omega, decide_true, prime, Bool.true_and]
      apply Evaluates.boolean_next (flag := true)
        (by simpa only [show radix ≤ n by omega, decide_true] using threshold) rfl rfl
      apply Evaluates.boolean_next (flag := true)
        (by simpa only [prime, decide_true] using primality) rfl rfl
      exact Evaluates.boolean_last truncated rfl
    · refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      simp only [referenceCheck, show radix ≤ n by omega, decide_true, prime, decide_false,
        Bool.and_false, Bool.false_and]
      apply Evaluates.boolean_next (flag := true)
        (by simpa only [show radix ≤ n by omega, decide_true] using threshold) rfl rfl
      exact Evaluates.boolean_stop (flag := false)
        (by simpa only [prime, decide_false] using primality) rfl rfl

end data.«project-euler-statements».data.py.project_euler_statements.p37
