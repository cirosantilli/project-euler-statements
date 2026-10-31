import data.«project-euler-statements».data.py.project_euler_statements.«p77.primes.source»

/-! The source search stops at the least prime-partition count exceeding the signed target. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p77
open FormalSW.PyAst HeapMemoCalls
open ProjectEulerStatements.PrimePartitions (primesUpTo count answer answer_spec answer_le)
set_option Elab.async false
variable {globals : Mutable.Globals}

theorem count_prime_sums.result (n : Int) (heap : Heap) :
    ReturnsRel (globals := globals) program cacheSpec "count_prime_sums" [integer n] heap
      (resultPost n (primesUpTo n.toNat) heap) := by
  let args := ((findFunctionIn program.body "count_prime_sums").getD ([], [])).1
  let body := ((findFunctionIn program.body "count_prime_sums").getD ([], [])).2
  let env := HeapCalls.functionEnv args body [integer n] globals
  have getN : env "n" = some (integer n) := by cases globals <;> rfl
  have primeCall : EvaluatesRel (globals := globals) program cacheSpec env
      (.call (.name "primes_up_to") [.name "n"]) heap
      (fun value after => ∃ address extra, value = .ref address ∧ after = heap ++ extra ∧
        after[address]? = some (.tuple (integers (primesUpTo n.toNat)))) := by
    apply EvaluatesRel.call (ArgumentsRel.fixed (.cons (Evaluates.lookup getN) .nil))
    rintro _ after ⟨rfl, sameHeap⟩
    subst after
    exact primes_up_to.result n heap
  apply BlockReturnsRel.function (args := args) (body := body) (by decide) rfl rfl
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.call (argumentPost := fun values after => ∃ address extra,
    values = [integer n, .ref address] ∧ after = heap ++ extra ∧
      after[address]? = some (.tuple (integers (primesUpTo n.toNat))))
  · apply ArgumentsRel.cons (Evaluates.lookup getN).rel
    rintro _ after ⟨rfl, sameHeap⟩
    subst after
    apply ArgumentsRel.cons primeCall
    rintro _ _ ⟨address, extra, rfl, rfl, found⟩
    exact ArgumentsRel.nil ⟨address, extra, rfl, rfl, found⟩
  · rintro _ _ ⟨address, extra, rfl, rfl, found⟩
    apply (go.result n (primesUpTo n.toNat) (heap ++ extra) address found).consequence
    rintro value after ⟨same, suffix, rfl⟩
    exact ⟨same, extra ++ suffix, by simp [List.append_assoc]⟩

namespace naive

private abbrev sourceBody : List Stmt :=
  [.ifThen (.compare (.call (.name "count_prime_sums") [.name "n"]) [(.gt, .name "target")])
      [.return (.name "n")] [],
    .augAssign (.name "n") .add (.constant (.int 1))]

private abbrev sourceLoop : Stmt := .whileDo (.constant (.bool true)) sourceBody []

def Post (target : Int) (heap : Heap) (value : Mutable.Value) (after : Heap) : Prop :=
  value = integer (answer target) ∧ ∃ extra, after = heap ++ extra

private theorem tested (target : Int) (n : Nat) (heap : Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (integer n)) (getTarget : env "target" = some (integer target)) :
    EvaluatesRel (globals := globals) program cacheSpec env
      (.compare (.call (.name "count_prime_sums") [.name "n"]) [(.gt, .name "target")]) heap
      (fun value after => value = .scalar (.bool (decide (target < (count n : Int)))) ∧
        ∃ extra, after = heap ++ extra) := by
  have called : EvaluatesRel (globals := globals) program cacheSpec env
      (.call (.name "count_prime_sums") [.name "n"]) heap
      (resultPost n (primesUpTo n) heap) := by
    apply EvaluatesRel.call (ArgumentsRel.fixed (.cons (Evaluates.lookup getN) .nil))
    rintro _ after ⟨rfl, sameHeap⟩
    subst after
    simpa only [Int.toNat_natCast] using count_prime_sums.result (n : Int) heap
  apply EvaluatesRel.compare (leftPost := resultPost n (primesUpTo n) heap)
    (rightPost := fun _ middle value after => value = integer target ∧ after = middle) called
  · intro av middle _
    exact (Evaluates.lookup getTarget).rel
  · rintro av middle bv after ⟨rfl, extra, rfl⟩ ⟨rfl, rfl⟩
    refine ⟨.scalar (.bool (decide (target < (count n : Int)))), _, ?_, cache_preserved _ _, rfl, extra, rfl⟩
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, ways, count, show ¬ (n : Int) < 0 by omega]

private theorem loop (target : Int) (n : Nat) (heap : Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (integer n)) (getTarget : env "target" = some (integer target))
    (lower : 2 ≤ n) (upper : n ≤ answer target) :
    BlockReturnsRel (globals := globals) program cacheSpec env [sourceLoop] heap (Post target heap) := by
  induction measure : answer target - n using Nat.strong_induction_on generalizing n heap env with
  | h remaining ih =>
      apply BlockReturnsRel.while_loop (Evaluates.constant (value := .bool true)).rel
      rintro _ after ⟨rfl, sameHeap⟩
      subst after
      refine ⟨true, rfl, ?_⟩
      apply BlockReturnsRel.branch (tested target n heap env getN getTarget)
      rintro _ _ ⟨rfl, extra, rfl⟩
      refine ⟨decide (target < (count n : Int)), rfl, ?_⟩
      by_cases over : target < (count n : Int)
      · have least : answer target ≤ n := answer_le target n ⟨lower, over⟩
        have same : n = answer target := by omega
        simp only [over, decide_true, if_true, List.singleton_append]
        apply BlockReturnsRel.return_value
        exact EvaluatesRel.lookup getN ⟨by simp [same], extra, rfl⟩
      · have before : n < answer target := by
          have exceeds := (answer_spec target).2
          by_contra notBefore
          have same : n = answer target := by omega
          exact over (by simpa [same] using exceeds)
        simp only [over, decide_false, Bool.false_eq_true, if_false, List.nil_append]
        apply BlockReturnsRel.augAssign getN (Evaluates.constant (value := .int 1)).rel
        rintro _ after ⟨rfl, sameHeap⟩
        subst after
        refine ⟨integer ((n : Int)+1), _, rfl, cache_preserved _ _, ?_⟩
        have rest := ih (answer target - (n+1)) (by omega) (n+1) (heap ++ extra)
          (HeapCalls.setLocal env "n" (integer ((n : Int)+1)))
          (by simp [HeapCalls.setLocal])
          (by simpa [HeapCalls.setLocal] using getTarget) (by omega) (by omega) rfl
        apply (rest.consequence ?_)
        rintro value after ⟨same, suffix, rfl⟩
        exact ⟨same, extra ++ suffix, by simp [List.append_assoc]⟩

/-- Every signed threshold terminates, using mathematical growth rather than a runtime bound. -/
theorem result (target : Int) (heap : Heap) :
    ReturnsRel (globals := globals) program cacheSpec "naive" [integer target] heap (Post target heap) := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let body := ((findFunctionIn program.body "naive").getD ([], [])).2
  let env := HeapCalls.functionEnv args body [integer target] globals
  apply BlockReturnsRel.function (args := args) (body := body) (by decide) rfl rfl
  apply BlockReturnsRel.assign (Evaluates.constant (value := .int 2)).rel
  rintro _ after ⟨rfl, sameHeap⟩
  subst after
  apply loop target 2 heap (HeapCalls.setLocal env "n" (integer 2))
    (by simp [HeapCalls.setLocal]) ?_ (by omega) (answer_spec target).1
  cases globals <;> rfl

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p77
