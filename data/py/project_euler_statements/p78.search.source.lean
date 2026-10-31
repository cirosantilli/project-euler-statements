import data.«project-euler-statements».data.py.project_euler_statements.«p78.partition.source»
import lang.py.FormalSW.MemoLoopProgress
import ProjectEulerStatements.Lib.PartitionSearch

/-! The cached reference returns the least qualifying index, or makes supported unbounded progress. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p78.naive
open FormalSW.PyAst MemoCalls
open ProjectEulerStatements.PartitionSearch
set_option Elab.async false

private abbrev sourceBody : List Stmt :=
  [.ifThen (.compare (.binOp (.call (.name "partition") [.name "n"]) .mod (.name "mod"))
      [(.eq, .constant (.int 0))]) [.return (.name "n")] [],
    .augAssign (.name "n") .add (.constant (.int 1))]

private abbrev sourceLoop : Stmt := .whileDo (.constant (.bool true)) sourceBody []

private theorem tested (modulus : Int) (positive : 0 < modulus) (n : Nat) (env : ScalarEnv)
    (getN : env "n" = some (.int n)) (getMod : env "mod" = some (.int modulus)) :
    Evaluates program ["partition_go"] cacheSpec env
      (.compare (.binOp (.call (.name "partition") [.name "n"]) .mod (.name "mod"))
        [(.eq, .constant (.int 0))])
      (.bool (decide ((ProjectEulerStatements.P76.countWays n n : Int) % modulus = 0))) := by
  have residue : Evaluates program ["partition_go"] cacheSpec env
      (.binOp (.call (.name "partition") [.name "n"]) .mod (.name "mod"))
      (.int ((ProjectEulerStatements.P76.countWays n n : Int) % modulus)) :=
    Evaluates.binary
      (Evaluates.call (.cons (Evaluates.lookup getN) .nil) (partition.result n))
      (Evaluates.lookup getMod)
      (by simp [scalarBinary, positive, show modulus ≠ 0 by omega])
  exact Evaluates.compare residue Evaluates.constant (by simp [scalarCompare, evalCmpOp])

private theorem loop (modulus : Int) (positive : 0 < modulus) (success : Success modulus)
    (n : Nat) (lower : 0 < n) (upper : n ≤ answer modulus success) (env : ScalarEnv)
    (getN : env "n" = some (.int n)) (getMod : env "mod" = some (.int modulus)) :
    BlockReturns program ["partition_go"] cacheSpec env [sourceLoop]
      (.int (answer modulus success)) := by
  induction measure : answer modulus success - n using Nat.strong_induction_on generalizing n env with
  | h size ih =>
      apply BlockReturns.while_loop (value := .bool true) Evaluates.constant
      change BlockReturns program ["partition_go"] cacheSpec env
        (sourceBody ++ [sourceLoop]) (.int (answer modulus success))
      have test := tested modulus positive n env getN getMod
      by_cases same : n = answer modulus success
      · have divides : (ProjectEulerStatements.P76.countWays n n : Int) % modulus = 0 := by
          simpa only [same] using (answer_spec modulus success).2
        apply BlockReturns.branch (value := .bool true)
          (by simpa only [divides, decide_true] using test)
        apply BlockReturns.return_value
        simpa only [same] using Evaluates.lookup (module := program) (memoized := ["partition_go"])
          (spec := cacheSpec) getN
      · have earlier : n < answer modulus success := by omega
        have absent := before_answer modulus success n lower earlier
        apply BlockReturns.branch (value := .bool false)
          (by simpa only [absent, decide_false] using test)
        apply BlockReturns.augAssign (value := .int (n+1 : Nat))
          (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant (by simp [scalarBinary]))
        apply ih (answer modulus success - (n+1)) (by omega) (n+1) (by omega) (by omega)
          (env.set "n" (.int (n+1 : Nat))) (by simp [ScalarEnv.set])
          (by simpa [ScalarEnv.set] using getMod) rfl

theorem result (modulus : Int) (positive : 0 < modulus) (success : Success modulus) :
    ReturnsValue program ["partition_go"] cacheSpec "naive" [.int modulus]
      (.int (answer modulus success)) := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let body := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := argumentEnv args [.int modulus]
  apply BlockReturns.function (args := args) (body := body) (by simp) rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply loop modulus positive success 1 (by omega) (answer_positive modulus success)
    (entry.set "n" (.int 1)) (by simp [ScalarEnv.set])
    (by simp [ScalarEnv.set]; rfl)

theorem diverges (modulus : Int) (positive : 0 < modulus) (none : ¬ Success modulus) :
    (sourceFunction program "naive" [.int modulus]).Diverges := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let body := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := argumentEnv args [.int modulus]
  let ready := entry.set "n" (.int 1)
  let invariant : ScalarEnv → Prop := fun env =>
    ∃ n : Nat, 0 < n ∧ env "n" = some (.int n) ∧ env "mod" = some (.int modulus)
  apply scalar_while_diverges program ["partition_go"] cacheSpec "naive" [.int modulus]
    args body [.assign [.name "n"] (.constant (.int 1))] sourceBody
    (by simp) rfl rfl rfl rfl invariant ready
  · exact BlockContinues.assign Evaluates.constant
  · exact ⟨1, by omega, by simp [ready, ScalarEnv.set], by simp [ready, ScalarEnv.set]; rfl⟩
  · intro env current
    obtain ⟨n, lower, getN, getMod⟩ := current
    have missing := absent modulus none n lower
    have test := tested modulus positive n env getN getMod
    have branch : BlockContinues program ["partition_go"] cacheSpec env (sourceBody.take 1) env := by
      apply BlockContinues.branch (value := .bool false)
        (by simpa only [missing, decide_false] using test)
      exact BlockContinues.nil
    have increment : BlockContinues program ["partition_go"] cacheSpec env
        [.augAssign (.name "n") .add (.constant (.int 1))] (env.set "n" (.int (n+1 : Nat))) :=
      BlockContinues.augAssign
        (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant (by simp [scalarBinary]))
    exact ⟨env.set "n" (.int (n+1 : Nat)), branch.append increment, n+1, by omega,
      by simp [ScalarEnv.set], by simpa [ScalarEnv.set] using getMod⟩

theorem returns_iff (modulus : Int) (positive : 0 < modulus) :
    (sourceFunction program "naive" [.int modulus]).Returns ↔ Success modulus := by
  classical
  constructor
  · rintro ⟨value, returned⟩
    by_contra none
    exact Execution.diverges_not_halts (diverges modulus positive none) ⟨.ok value, returned⟩
  · intro success
    exact (result modulus positive success).returns

end data.«project-euler-statements».data.py.project_euler_statements.p78.naive
