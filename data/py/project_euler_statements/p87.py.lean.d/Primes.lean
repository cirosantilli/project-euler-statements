import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p87.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.HeapCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p87
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
abbrev program := P87Ast.module
abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
def numbers (items : List Int) : List Mutable.Value := items.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 3 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["primes_below", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

namespace primes_below
def values (limit : Nat) : List Nat := (List.range limit).filter fun n => decide (Nat.Prime n)
private def body (address : Nat) : List Stmt :=
  [.ifThen (.call (.name "is_prime") [.name "n"]) [.comprehensionAppend address (.name "n")] []]

private theorem loop (first count stop : Nat) (length : first + count = stop)
    (base : Mutable.Heap) (items : List Int) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "n" first stop 1 (body base.length) []]
      (base ++ [.list (numbers items)]) finalEnv
      (base ++ [.list (numbers (items ++ ((List.range' first count).filter fun n => decide (Nat.Prime n)).map Int.ofNat))]) := by
  induction count generalizing first items env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.filter_nil, List.map_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "n" (number first)
      have tested : Evaluates program bound (.call (.name "is_prime") [.name "n"])
          (base ++ [.list (numbers items)]) (flag (decide (Nat.Prime first)))
          (base ++ [.list (numbers items)]) := by
        apply Evaluates.call (values := [number first]) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil)
        exact (common.is_prime.heap_result first _).extend common_extension
      by_cases prime : Nat.Prime first
      · have emitted : BlockContinues program bound (body base.length)
            (base ++ [.list (numbers items)]) bound (base ++ [.list (numbers (items ++ [(first : Int)]))]) := by
          apply BlockContinues.branch (flag := true) tested (by simp [prime, Mutable.truth, scalarTruth])
          have looked : Evaluates program bound (.name "n")
              (ProjectEulerSolutions.HeapCollection.working base (numbers items) []) (number first)
              (ProjectEulerSolutions.HeapCollection.working base (numbers items) []) :=
            Evaluates.lookup (by simp [bound, setLocal])
          simpa only [ProjectEulerSolutions.HeapCollection.working, numbers, List.map_append,
            List.map_cons, List.map_nil, List.append_nil] using
            ProjectEulerSolutions.HeapCollection.emit base (numbers items) [] [] (number first)
              (by simpa only [List.append_nil] using looked)
        obtain ⟨finalEnv, rest⟩ := ih (first + 1) (by omega) (items ++ [(first : Int)]) bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, body,
          Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.filter_cons,
          show decide (Nat.Prime first) = true by simp [prime], if_true, List.map_cons,
          Int.natCast_add, Int.natCast_one, List.append_assoc, List.singleton_append] using emitted.append rest
      · have skipped : BlockContinues program bound (body base.length)
            (base ++ [.list (numbers items)]) bound (base ++ [.list (numbers items)]) :=
          BlockContinues.branch (flag := false) tested (by simp [prime, Mutable.truth, scalarTruth]) .nil
        obtain ⟨finalEnv, rest⟩ := ih (first + 1) (by omega) items bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, body,
          Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.filter_cons,
          show decide (Nat.Prime first) = false by simp [prime], Int.natCast_add,
          Int.natCast_one] using skipped.append rest

/-- Filtering the entire signed range terminates and allocates exactly one prime list. -/
theorem result (limit : Int) (heap : Mutable.Heap) :
    ReturnsValue program "primes_below" [number limit] heap (.ref heap.length)
      (heap ++ [.list (numbers ((values limit.toNat).map Int.ofNat))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases below : limit < 0
  · have empty : limit.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    apply Evaluates.list_comp_range (.cons (Evaluates.lookup rfl) .nil) rfl
    simp only [empty, values, List.range_zero, List.filter_nil, List.map_nil, numbers]
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  · lift limit to Nat using (by omega : 0 ≤ limit)
    obtain ⟨finalEnv, executed⟩ := loop 0 limit limit (by omega) heap [] _
    apply Evaluates.list_comp_range (finalEnv := finalEnv) (.cons (Evaluates.lookup rfl) .nil) rfl
    simpa only [numbers, values, Int.toNat_natCast, List.range_eq_range', List.nil_append, List.map_nil] using executed

theorem «Returns» (limit : Int) : (HeapCalls.call program "primes_below" [number limit] []).Returns :=
  (result limit []).returns

theorem «Supported» (limit : Int) : (HeapCalls.call program "primes_below" [number limit] []).Supported :=
  («Returns» limit).supported
end primes_below

end data.«project-euler-statements».data.py.project_euler_statements.p87
