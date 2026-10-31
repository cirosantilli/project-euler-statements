import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Value
import ProjectEulerSolutions.Lib.HeapCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false

abbrev code : List Stmt := executableBody ((findFunctionIn program.body "int_to_roman_aux").getD ([], [])).2
abbrev loopCode : List Stmt := match code[2]'(by decide) with
  | .forIn _ _ body _ => body
  | _ => []

structure Locals (env : HeapCalls.Env) (n denomination tokenAddress outputAddress : Nat) : Prop where
  remaining : env "n" = some (number n)
  denomination : env "v" = some (number denomination)
  token : env "cs" = some (.ref tokenAddress)
  output : env "out" = some (.ref outputAddress)

/-- The reference while loop emits quotient-many tokens and leaves the exact remainder. -/
theorem repeat_token (denomination : Nat) (positive : 0 < denomination)
    (token : List Mutable.Value) (tokenAddress : Nat) (base : Mutable.Heap)
    (found : base[tokenAddress]? = some (.list token)) (n : Nat) (output : List Mutable.Value)
    (env : HeapCalls.Env) (ready : Locals env n denomination tokenAddress base.length) :
    ∃ finalEnv,
      BlockContinues program env loopCode (HeapCollection.working base output []) finalEnv
        (HeapCollection.working base (output ++ copies token (n / denomination)) []) ∧
      Locals finalEnv (n % denomination) denomination tokenAddress base.length ∧
      ∀ name, name ≠ "n" → name ≠ "out" → finalEnv name = env name := by
  let heap := HeapCollection.working base output []
  have tested : Evaluates program env (.compare (.name "n") [(.gtE, .name "v")]) heap
      (.scalar (.bool (decide (denomination ≤ n)))) heap := by
    apply Evaluates.compare (Evaluates.lookup ready.remaining) (Evaluates.lookup ready.denomination)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases active : denomination ≤ n
  · let appended := setLocal env "out" (.ref base.length)
    let advanced := setLocal appended "n" (number (n - denomination))
    have extended : BlockContinues program env [.augAssign (.name "out") .add (.name "cs")]
        heap appended (HeapCollection.working base (output ++ token) []) := by
      apply BlockContinues.augAssign ready.output (Evaluates.lookup ready.token)
      have readToken : heap[tokenAddress]? = some (.list token) :=
        HeapCollection.prefix_found base _ tokenAddress _ found
      simpa only [heap, HeapCollection.store] using
        inplace_add_lists heap base.length tokenAddress output token (HeapCollection.found base output []) readToken
    have decreased : BlockContinues program appended [.augAssign (.name "n") .sub (.name "v")]
        (HeapCollection.working base (output ++ token) []) advanced
        (HeapCollection.working base (output ++ token) []) := by
      apply BlockContinues.augAssign (left := number n) (right := number denomination)
        (by simpa [appended, setLocal] using ready.remaining)
        (Evaluates.lookup (by simpa [appended, setLocal] using ready.denomination))
      simp [inplace, Mutable.binary, scalarBinary, number, Nat.cast_sub active]
    have advancedReady : Locals advanced (n - denomination) denomination tokenAddress base.length :=
      ⟨by simp [advanced, setLocal], by simpa [advanced, appended, setLocal] using ready.denomination,
        by simpa [advanced, appended, setLocal] using ready.token, by simp [advanced, appended, setLocal]⟩
    obtain ⟨finalEnv, continued, finalReady, stable⟩ := repeat_token denomination positive token tokenAddress base found
      (n - denomination) (output ++ token) advanced advancedReady
    have quotient := Nat.div_eq_sub_div positive active
    have remainder := Nat.mod_eq_sub_mod active
    refine ⟨finalEnv, ?_, by simpa only [remainder] using finalReady, ?_⟩
    · rw [quotient, copies_succ, ← List.append_assoc]
      apply BlockContinues.while_loop (flag := true) tested (by simp [Mutable.truth, scalarTruth, active])
      simpa only [Calls.loopContinuation,
        show Calls.loopControl [.augAssign (.name "out") .add (.name "cs"), .augAssign (.name "n") .sub (.name "v")] = false from rfl,
        if_false] using extended.append (decreased.append continued)
    · intro name notN notOut
      rw [stable name notN notOut]
      simp [advanced, appended, setLocal, notN, notOut]
  · have small : n < denomination := by omega
    refine ⟨env, ?_, ?_, fun _ _ _ => rfl⟩
    · simp only [Nat.div_eq_of_lt small, copies_zero, List.append_nil]
      exact BlockContinues.while_loop (flag := false) tested (by simp [Mutable.truth, scalarTruth, active]) .nil
    · simpa only [Nat.mod_eq_of_lt small] using ready
termination_by n
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
