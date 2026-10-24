import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p53.py.ast»
import ProjectEulerSolutions.Lib.BinomialSelections
import lang.py.FormalSW.SumCalls
import lang.py.FormalSW.LoopCalls

/-! Source termination and exact counting for every signed reference bound and threshold. -/
set_option Elab.async false
namespace data.«project-euler-statements».data.py.project_euler_statements.p53
open FormalSW.PyAst FormalSW.PyAst.HeapCalls ProjectEulerSolutions.BinomialSelections
private abbrev program := P53Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def test : Expr := .compare (.call (.name "comb") [.name "n", .name "r"]) [(.gt, .name "threshold")]
private def innerBody : List Stmt := comprehensionFilters [test] (sumBody (.constant (.int 1)) [])
private def outerBody : List Stmt := sumBody (.constant (.int 1))
  [("r", .call (.name "range") [.binOp (.name "n") .add (.constant (.int 1))], [test])]
private def count (n : Nat) (threshold : Int) (first length : Nat) : Nat :=
  ((List.range' first length).filter (fun r => decide (threshold < (Nat.choose n r : Int)))).length

private theorem tested (n r : Nat) (threshold : Int) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getN : env "n" = some (number n)) (getR : env "r" = some (number r))
    (getThreshold : env "threshold" = some (number threshold)) :
    Evaluates program env test heap (flag (decide (threshold < (Nat.choose n r : Int)))) heap := by
  apply Evaluates.compare (av := number (Nat.choose n r)) (bv := number threshold) (middle := heap) (afterRight := heap)
  · apply Evaluates.library_call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getR) .nil)) rfl
    change some (Except.map Mutable.Value.scalar (Math.combCall [.int n, .int r]), heap) = _
    rw [Math.combCall_naturals, comb_eq_choose]
    rfl
  · exact Evaluates.lookup getThreshold
  · rfl

private def StableInner (before after : HeapCalls.Env) : Prop :=
  ∀ name, name ≠ "r" → name ≠ sumAccumulator → after name = before name

private theorem inner (n first length stop : Nat) (bounded : first+length = stop) (threshold initial : Int)
    (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getN : env "n" = some (number n)) (getThreshold : env "threshold" = some (number threshold))
    (getTotal : env sumAccumulator = some (number initial)) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "r" first stop 1 innerBody []] heap finalEnv heap ∧
      StableInner env finalEnv ∧ finalEnv sumAccumulator = some (number (initial + count n threshold first length)) := by
  induction length generalizing first initial env with
  | zero =>
      refine ⟨env, BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil, fun _ _ _ => rfl, ?_⟩
      simpa [count] using getTotal
  | succ length ih =>
      let bound := setLocal env "r" (number first)
      have boundN : bound "n" = some (number n) := by simpa [bound, setLocal] using getN
      have boundThreshold : bound "threshold" = some (number threshold) := by simpa [bound, setLocal] using getThreshold
      have boundTotal : bound sumAccumulator = some (number initial) := by simpa [bound, setLocal, sumAccumulator] using getTotal
      have check := tested n first threshold bound heap boundN (by simp [bound, setLocal]) boundThreshold
      by_cases hit : threshold < (Nat.choose n first : Int)
      · let ready := setLocal bound sumAccumulator (number (initial+1))
        obtain ⟨finalEnv, continued, stable, total⟩ := ih (first+1) (by omega) (initial+1) ready
          (by simpa [ready, setLocal, sumAccumulator] using boundN)
          (by simpa [ready, setLocal, sumAccumulator] using boundThreshold) (by simp [ready, setLocal])
        refine ⟨finalEnv, ?_, ?_, ?_⟩
        · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
          apply BlockContinues.branch_next (flag := true) (by simpa only [hit, decide_true] using check) rfl
          have assigned : BlockContinues program bound (sumBody (.constant (.int 1)) []) heap ready heap := by
            apply BlockContinues.assign
            exact Evaluates.binary (Evaluates.lookup boundTotal) Evaluates.constant (by simp [Mutable.binary, scalarBinary])
          simpa [innerBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, List.append_assoc, Nat.cast_add] using assigned.append continued
        · intro name notR notTotal
          exact (stable name notR notTotal).trans (by simp [ready, bound, setLocal, notR, notTotal])
        · simpa [count, List.range'_succ, hit, Int.add_assoc, Int.add_comm] using total
      · obtain ⟨finalEnv, continued, stable, total⟩ := ih (first+1) (by omega) initial bound boundN boundThreshold boundTotal
        refine ⟨finalEnv, ?_, ?_, ?_⟩
        · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
          apply BlockContinues.branch_next (flag := false) (by simpa only [hit, decide_false] using check) rfl
          simpa [innerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            comprehensionFilters, sumBody, Nat.cast_add] using continued
        · intro name notR notTotal
          exact (stable name notR notTotal).trans (by simp [bound, setLocal, notR])
        · simpa [count, List.range'_succ, hit] using total

private theorem outer (first length stop : Nat) (bounded : first+length = stop) (threshold initial : Int)
    (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getThreshold : env "threshold" = some (number threshold)) (getTotal : env sumAccumulator = some (number initial)) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "n" first stop 1 outerBody []] heap finalEnv heap ∧
      finalEnv "threshold" = some (number threshold) ∧ finalEnv sumAccumulator = some (number (initial + series first length threshold)) := by
  induction length generalizing first initial env with
  | zero =>
      exact ⟨env, BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil, getThreshold, by simpa using getTotal⟩
  | succ length ih =>
      let bound := setLocal env "n" (number first)
      obtain ⟨ready, counted, stable, subtotal⟩ := inner first 0 (first+1) (first+1) (by omega) threshold initial bound heap
        (by simp [bound, setLocal]) (by simpa [bound, setLocal] using getThreshold)
        (by simpa [bound, setLocal, sumAccumulator] using getTotal)
      have readyThreshold : ready "threshold" = some (number threshold) :=
        (stable "threshold" (by decide) (by decide)).trans (by simpa [bound, setLocal] using getThreshold)
      have subtotal : ready sumAccumulator = some (number (initial + row first threshold)) := by
        simpa only [count, row, List.range_eq_range'] using subtotal
      obtain ⟨finalEnv, continued, finalThreshold, total⟩ := ih (first+1) (by omega) (initial + row first threshold) ready readyThreshold subtotal
      refine ⟨finalEnv, ?_, finalThreshold, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        have countedSource : BlockContinues program bound outerBody heap ready heap := by
          apply BlockContinues.for_range (middle := heap) (values := [number (first+1 : Nat)])
            (start := 0) (stop := ((first+1 : Nat) : Int)) (stride := 1)
          · refine .cons ?_ .nil
            exact Evaluates.binary (av := number first) (bv := number 1) (middle := heap) (afterRight := heap)
              (Evaluates.lookup (by simp [bound, setLocal])) Evaluates.constant (by simp [Mutable.binary, scalarBinary])
          · rfl
          · exact counted
        simpa [outerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Nat.cast_add] using countedSource.append continued
      · simpa only [series_succ, Nat.cast_add, ← Int.add_assoc] using total

namespace naive
/-- Both generator loops terminate for every signed bound and threshold, with their exact count. -/
theorem result (limit threshold : Int) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number limit, number threshold] heap (number (answer limit threshold)) heap := by
  let entry := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit, number threshold] []
  let generators : List (String × Expr × List Expr) :=
    [("n", .call (.name "range") [.constant (.int 1), .binOp (.name "limit_n") .add (.constant (.int 1))], []),
      ("r", .call (.name "range") [.binOp (.name "n") .add (.constant (.int 1))], [test])]
  let ready := setLocal (comprehensionEnv entry generators) sumAccumulator (number 0)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap)
    (values := [number 1, number (limit+1)]) (first := 1) (stop := limit+1) (stride := 1)
  · refine .cons Evaluates.constant (.cons ?_ .nil)
    exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl
  · rfl
  · exact Evaluates.constant
  · rfl
  · by_cases positive : 0 ≤ limit
    · lift limit to Nat using positive
      obtain ⟨finalEnv, executed, _, total⟩ := outer 1 limit (limit+1) (by omega) threshold 0 ready heap rfl rfl
      apply executed.returns
      apply BlockReturns.return_value
      simpa [answer] using Evaluates.lookup total
    · have empty : limit.toNat = 0 := by omega
      simp only [answer, empty, series_zero]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup (by simp [setLocal]))

theorem «Returns» (limit threshold : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit, .int threshold]).Returns := (result limit threshold []).scalar_returns

theorem «Supported» (limit threshold : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit, .int threshold]).Supported := («Returns» limit threshold).supported
end naive
end data.«project-euler-statements».data.py.project_euler_statements.p53
