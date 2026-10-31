import data.«project-euler-statements».data.py.project_euler_statements.«p77.go.source»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.GeneratorCalls

/-! The original generator filters the complete signed range before constructing its immutable tuple. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p77
open FormalSW.PyAst
open ProjectEulerStatements.PrimePartitions (primesUpTo)
set_option Elab.async false
variable {globals : Mutable.Globals}

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  have extension : Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module := by
    apply Calls.Extends.prepend
    · intro name member
      change name ∈ ["primes_up_to", "go", "count_prime_sums", "naive"] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    · intro name member
      change name ∈ ([] : List String) at member
      simp at member
  exact ⟨extension.functions, extension.libraries⟩

private theorem common_disjoint : HeapMemoCalls.CacheDisjoint program CommonAst.module := by
  intro name cached
  change name ∈ ["go"] at cached
  have same : name = "go" := List.mem_singleton.mp cached
  subst name
  exact ⟨by decide, by decide, by decide⟩

namespace primes_up_to
open HeapCalls

private def loopBody (address : Nat) : List Stmt :=
  [.ifThen (.call (.name "is_prime") [.name "x"]) [.comprehensionAppend address (.name "x")] []]

private theorem loop (first count stop : Nat) (length : first + count = stop)
    (base : Mutable.Heap) (items : List Nat) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues (globals := globals) CommonAst.module env
      [.rangeStepLoop "x" first stop 1 (loopBody base.length) []]
      (base ++ [.list (integers items)]) finalEnv
      (base ++ [.list (integers (items ++ ((List.range' first count).filter Nat.Prime)))]) := by
  induction count generalizing first items env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.filter_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "x" (integer first)
      have tested : Evaluates (globals := globals) CommonAst.module bound
          (.call (.name "is_prime") [.name "x"])
          (base ++ [.list (integers items)]) (.scalar (.bool (decide (Nat.Prime first))))
          (base ++ [.list (integers items)]) := by
        apply Evaluates.call (values := [integer first]) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil)
        exact common.is_prime.heap_result first _ globals
      by_cases prime : Nat.Prime first
      · have emitted : BlockContinues (globals := globals) CommonAst.module bound (loopBody base.length)
            (base ++ [.list (integers items)]) bound (base ++ [.list (integers (items ++ [first]))]) := by
          apply BlockContinues.branch (flag := true) tested (by simp [prime, Mutable.truth, scalarTruth])
          have write := BlockContinues.comprehension_append (globals := globals) (module := CommonAst.module)
            (env := bound) (address := base.length) (heap := base ++ [.list (integers items)])
            (Evaluates.lookup (name := "x") (value := integer first) (by simp [bound, setLocal]))
            (by simp : (base ++ [.list (integers items)])[base.length]? = some (.list (integers items)))
          simpa [integers, List.map_append] using write
        obtain ⟨finalEnv, rest⟩ := ih (first + 1) (by omega) (items ++ [first]) bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, loopBody,
          Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.filter_cons,
          show decide (Nat.Prime first) = true by simp [prime], if_true,
          Int.natCast_add, Int.natCast_one, List.append_assoc, List.singleton_append] using emitted.append rest
      · have skipped : BlockContinues (globals := globals) CommonAst.module bound (loopBody base.length)
            (base ++ [.list (integers items)]) bound (base ++ [.list (integers items)]) :=
          BlockContinues.branch (flag := false) tested (by simp [prime, Mutable.truth, scalarTruth]) .nil
        obtain ⟨finalEnv, rest⟩ := ih (first + 1) (by omega) items bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, loopBody,
          Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.filter_cons,
          show decide (Nat.Prime first) = false by simp [prime], if_false,
          Int.natCast_add, Int.natCast_one] using skipped.append rest

private abbrev generators : List (Expr × Expr × List Expr) :=
  [(.name "x", .call (.name "range") [.binOp (.name "n") .add (.constant (.int 1))],
    [.call (.name "is_prime") [.name "x"]])]

private theorem collected (n : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (integer n)) :
    Evaluates (globals := globals) CommonAst.module env
      (.consumeGenerator (.builtinCall .list []) (.name "x") generators) heap (.ref heap.length)
      (heap ++ [.list (integers (primesUpTo n.toNat))]) := by
  have executed : ∃ finalEnv, BlockContinues (globals := globals) CommonAst.module
      (comprehensionTargetsEnv env generators)
      [.rangeStepLoop "x" 0 (n+1) 1 (loopBody heap.length) []]
      (heap ++ [.list []]) finalEnv (heap ++ [.list (integers (primesUpTo n.toNat))]) := by
    by_cases negative : n < 0
    · have empty : n.toNat = 0 := by omega
      refine ⟨comprehensionTargetsEnv env generators, ?_⟩
      simp only [empty, primesUpTo, integers]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
    · lift n to Nat using (by omega : 0 ≤ n)
      obtain ⟨finalEnv, executed⟩ := loop 0 (n+1) (n+1) (by omega) heap []
        (comprehensionTargetsEnv env generators)
      refine ⟨finalEnv, ?_⟩
      simpa [integers, primesUpTo, List.range_eq_range'] using executed
  obtain ⟨finalEnv, executed⟩ := executed
  apply Evaluates.consume_generator_list
  apply GeneratorCollects.range (values := [integer (n+1)]) (finalEnv := finalEnv)
    (collectedHeap := heap ++ [.list (integers (primesUpTo n.toNat))])
    (.cons (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant rfl) .nil) rfl
  · exact executed
  · exact ⟨rfl, rfl⟩

/-- The private list collector and optional empty-tuple reuse preserve the caller's heap. -/
theorem result (n : Int) (heap : Mutable.Heap) :
    HeapMemoCalls.ReturnsRel (globals := globals) program cacheSpec "primes_up_to" [integer n] heap
      (fun value after => ∃ address extra, value = .ref address ∧ after = heap ++ extra ∧
        after[address]? = some (.tuple (integers (primesUpTo n.toNat)))) := by
  let args := ((findFunctionIn program.body "primes_up_to").getD ([], [])).1
  let body := ((findFunctionIn program.body "primes_up_to").getD ([], [])).2
  let env := functionEnv args body [integer n] globals
  have getN : env "n" = some (integer n) := by cases globals <;> rfl
  let middle := heap ++ [.list (integers (primesUpTo n.toNat))]
  obtain ⟨address, extra, allocated, found⟩ := tuple_allocation (integers (primesUpTo n.toNat)) middle
  have tupleRun : Evaluates (globals := globals) CommonAst.module env
      (.consumeGenerator (.builtinCall .tuple []) (.name "x") generators) heap
      (.ref address) (middle ++ extra) := by
    apply Evaluates.consume_generator_tuple (collected n heap env getN)
    simpa [primitive, Mutable.sequence, middle] using allocated
  apply HeapMemoCalls.BlockReturnsRel.function (args := args) (body := body) (by decide) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.return_value
  apply (HeapMemoCalls.Evaluates.from_heap common_extension common_disjoint tupleRun (cache_preserved _ _)).rel.consequence
  rintro value after ⟨rfl, rfl⟩
  exact ⟨address, [.list (integers (primesUpTo n.toNat))] ++ extra, rfl,
    by simp [middle, List.append_assoc], found⟩

end primes_up_to
end data.«project-euler-statements».data.py.project_euler_statements.p77
