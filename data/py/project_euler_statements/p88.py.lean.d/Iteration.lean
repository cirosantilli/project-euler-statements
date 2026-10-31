import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».State

namespace data.«project-euler-statements».data.py.project_euler_statements.p88
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

/-- One factor updates its minimum and executes all of its accepted descendants. -/
theorem iteration (maxSize limit : Nat) (before : List Nat) (valid : Admissible before)
    (factor : Nat) (lower : 2 ≤ factor) (inside : before.prod * factor ≤ limit)
    (descendants : Descendants maxSize limit before)
    (base : Mutable.Heap) (best : List Nat) (length : best.length = maxSize + 1)
    (env : HeapCalls.Env) (ready : Locals env maxSize limit before base.length)
    (getFactor : env "f" = some (number factor)) :
    BlockContinues program env (dfsBody.take 6) (working base best) (measuredEnv env before factor)
      (working base (accumulate (branch maxSize limit before.prod before.sum before.length factor) best)) := by
  let measured := measuredEnv env before factor
  let size := effectiveSize (before ++ [factor])
  have sizeFormula : size = before.length + 1 + before.prod * factor - (before.sum + factor) := by
    simp [size, effectiveSize]
  have measuredReady := ready.measured factor
  have getSize : measured "k" = some (number size) := measured_lookup env before factor
  have getValue : measured "new_prod" = some (number (before.prod * factor)) := by
    simp [measured, measuredEnv, setLocal]
  have arithmetic := measure_factor before factor valid lower env (working base best)
    ready.product ready.summ ready.terms getFactor
  apply arithmetic.append
  change BlockContinues program measured ((dfsBody.drop 4).take 2) (working base best) measured _
  by_cases accepted : size ≤ maxSize
  · let updated := relax best (size, before.prod * factor)
    have improved := improve maxSize best size (before.prod * factor) accepted (by omega)
      base measured measuredReady.table measuredReady.maximum getSize getValue
    have returned := descendants factor lower inside base updated (by simpa [updated, relax_length] using length)
    have called : Evaluates program measured
        (.call (.name "dfs") [.name "f", .name "new_prod", .name "new_sum", .name "new_terms",
          .name "k_max", .name "limit", .name "best"])
        (working base updated) (.ref base.length)
        (working base (accumulate
          (search maxSize limit factor (before.prod * factor) (before.sum + factor) (before.length + 1)) updated)) := by
      apply Evaluates.call (values := [number factor, number (before.prod * factor),
        number (before.sum + factor), number (before.length + 1), number maxSize, number limit, .ref base.length])
      · exact .cons (Evaluates.lookup (by simpa [measured, measuredEnv, setLocal] using getFactor))
          (.cons (Evaluates.lookup getValue)
          (.cons (Evaluates.lookup (by simp [measured, measuredEnv, setLocal]))
          (.cons (Evaluates.lookup (by simp [measured, measuredEnv, setLocal]))
          (.cons (Evaluates.lookup measuredReady.maximum)
          (.cons (Evaluates.lookup measuredReady.bound)
          (.cons (Evaluates.lookup measuredReady.table) .nil))))))
      · simpa [SearchReturns] using returned
    have recursed : BlockContinues program measured [dfsBody[5]'(by decide)]
        (working base updated) measured
        (working base (accumulate
          (search maxSize limit factor (before.prod * factor) (before.sum + factor) (before.length + 1)) updated)) := by
      apply BlockContinues.branch (flag := true)
        (size_evaluate size maxSize measured (working base updated) getSize measuredReady.maximum)
        (by simp [Mutable.truth, scalarTruth, accepted])
      exact BlockContinues.discard called
    rw [branch, ← sizeFormula, if_pos accepted]
    exact improved.append recursed
  · rw [branch, ← sizeFormula, if_neg accepted]
    exact reject maxSize size (by omega) measured (working base best) getSize measuredReady.maximum

end data.«project-euler-statements».data.py.project_euler_statements.p88
