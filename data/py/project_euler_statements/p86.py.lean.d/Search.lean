import data.«project-euler-statements».data.py.project_euler_statements.«p86.py.lean.d».Layer
import ProjectEulerSolutions.Lib.CuboidSearch

namespace data.«project-euler-statements».data.py.project_euler_statements.p86
open FormalSW.PyAst Calls ProjectEulerSolutions.CuboidRoute
set_option Elab.async false

abbrev searchCondition : Expr := .compare (.name "total") [(.ltE, .name "target")]
abbrev searchBody : List Stmt :=
  [.augAssign (.name "c") .add (.constant (.int 1)),
   .augAssign (.name "total") .add (.call (.name "count_new_cuboids") [.name "c"])]

theorem search_result (target : Int) (c : Nat) (env : ScalarEnv)
    (getTarget : env "target" = some (.int target)) (getC : env "c" = some (number c))
    (getTotal : env "total" = some (number (total c))) :
    BlockReturns program env [.whileDo searchCondition searchBody [], .return (.name "c")]
      (number (scan target c)) := by
  have tested : Evaluates program env searchCondition (.bool (decide ((total c : Int) ≤ target))) := by
    apply Evaluates.compare (Evaluates.lookup getTotal) (Evaluates.lookup getTarget)
    simp [scalarCompare, evalCmpOp]
  by_cases active : (total c : Int) ≤ target
  · let advanced := env.set "c" (number (c + 1))
    let updated := advanced.set "total" (number (total (c + 1)))
    have continued := search_result target (c + 1) updated
      (by simpa [updated, advanced, ScalarEnv.set] using getTarget)
      (by simp [updated, advanced, ScalarEnv.set]) (by simp [updated, ScalarEnv.set])
    rw [scan, dif_pos active]
    apply BlockReturns.while_loop (value := .bool true) (by simpa only [active, decide_true] using tested)
    apply BlockReturns.augAssign (value := number (c + 1))
      (Evaluates.binary (Evaluates.lookup getC) Evaluates.constant (by simp [scalarBinary, number]))
    apply BlockReturns.augAssign (value := number (total (c + 1)))
    · apply Evaluates.binary (av := number (total c)) (bv := number (exhaustiveLayer (c + 1)))
      · exact Evaluates.lookup (by simpa [advanced, ScalarEnv.set] using getTotal)
      · exact Evaluates.call (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil)
          (count_new_cuboids.result (c + 1))
      · simp [scalarBinary, number, total]
    exact continued
  · rw [scan, dif_neg active]
    apply BlockReturns.while_loop (value := .bool false) (by simpa only [active, decide_false] using tested)
    exact BlockReturns.return_value (Evaluates.lookup getC)
termination_by searchBound target - c
decreasing_by
  have := active_below_bound target c active
  omega

/-- The actual exhaustive Python search returns the least qualifying side bound. -/
theorem naive.result (target : Int) :
    ReturnsValue program "naive" [.int target] (number (answer target)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := number 0) Evaluates.constant
  apply BlockReturns.assign (value := number 0) Evaluates.constant
  exact search_result target 0 _ rfl rfl rfl

end data.«project-euler-statements».data.py.project_euler_statements.p86
