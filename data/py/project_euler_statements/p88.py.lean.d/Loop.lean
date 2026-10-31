import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Iteration

namespace data.«project-euler-statements».data.py.project_euler_statements.p88
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

/-- The source while loop visits exactly the remaining factors, preserving the caller prefix. -/
theorem loop (maxSize limit : Nat) (before : List Nat) (valid : Admissible before)
    (factor : Nat) (lower : 2 ≤ factor) (descendants : Descendants maxSize limit before)
    (base : Mutable.Heap) (best : List Nat) (length : best.length = maxSize + 1)
    (env : HeapCalls.Env) (ready : Locals env maxSize limit before base.length)
    (getFactor : env "f" = some (number factor)) :
    ∃ finalEnv, BlockContinues program env [dfsCode[2]'(by decide)] (working base best) finalEnv
      (working base (accumulate (search maxSize limit factor before.prod before.sum before.length) best)) ∧
      Locals finalEnv maxSize limit before base.length := by
  have positive := product_positive before valid
  have tested : Evaluates program env (.compare (.name "f") [(.ltE, .name "max_f")])
      (working base best) (.scalar (.bool (decide (factor ≤ limit / before.prod)))) (working base best) := by
    apply Evaluates.compare (Evaluates.lookup getFactor) (Evaluates.lookup ready.last)
    change (some (.ok (.scalar (.bool (decide ((factor : Int) ≤ ((limit / before.prod : Nat) : Int))))),
      working base best) : Option (Except ExceptionObject Mutable.Value × Mutable.Heap)) = _
    simp only [Int.ofNat_le]
  by_cases active : factor ≤ limit / before.prod
  · have inside : before.prod * factor ≤ limit := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < before.prod)).mp active
    let updated := accumulate (branch maxSize limit before.prod before.sum before.length factor) best
    let measured := measuredEnv env before factor
    let advanced := setLocal measured "f" (number (factor + 1))
    have measuredReady := ready.measured factor
    have advancedReady := measuredReady.factor (factor + 1)
    have incremented : BlockContinues program measured [dfsBody[6]'(by decide)]
        (working base updated) advanced (working base updated) := by
      apply BlockContinues.augAssign (left := number factor) (right := number 1)
        (by simpa [measured, measuredEnv, setLocal] using getFactor) Evaluates.constant
      simp [inplace, Mutable.binary, scalarBinary, number]
    obtain ⟨finalEnv, continued, finalReady⟩ := loop maxSize limit before valid (factor + 1) (by omega)
      descendants base updated (by simpa [updated, accumulate_length] using length)
      advanced advancedReady (by simp [advanced, setLocal])
    refine ⟨finalEnv, ?_, finalReady⟩
    rw [accumulate_step maxSize limit factor before.prod before.sum before.length best (by omega) lower active]
    apply BlockContinues.while_loop (flag := true) tested (by simp [Mutable.truth, scalarTruth, active])
    have iterated := iteration maxSize limit before valid factor lower inside descendants base best length env ready getFactor
    simpa only [Calls.loopContinuation, show Calls.loopControl dfsBody = false from rfl, if_false] using
      iterated.append (incremented.append continued)
  · refine ⟨env, ?_, ready⟩
    rw [search_done maxSize limit factor before.prod before.sum before.length (by omega) lower (by omega)]
    exact BlockContinues.while_loop (flag := false) tested (by simp [Mutable.truth, scalarTruth, active]) .nil
termination_by limit / before.prod + 1 - factor
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p88
