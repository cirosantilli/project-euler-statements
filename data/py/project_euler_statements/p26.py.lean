import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p26.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P26
import ProjectEulerStatements.Lib.ArgMaximum

namespace data.«project-euler-statements».data.py.project_euler_statements.p26
open FormalSW.PyAst FormalSW.PyAst.Calls
open ProjectEulerStatements.P26
private abbrev program := P26Ast.module


private def stripLoop : List Stmt :=
  (executableBody ((findFunctionIn program.body "strip_factor").getD ([], [])).2).drop 1

private theorem strip_loop (p n : Nat) (large : 1 < p) (env : ScalarEnv)
    (getP : env "p" = some (.int p)) (getN : env "n" = some (.int n)) :
    BlockReturns program env stripLoop (.int (stripFactor p n)) := by
  induction n using Nat.strong_induction_on generalizing env with
  | h n ih =>
      by_cases zero : n = 0
      · subst n
        have result : stripFactor p 0 = 0 := by rw [stripFactor]; simp
        rw [result]
        apply BlockReturns.while_loop (value := .int 0)
        · exact Evaluates.boolean_stop (Evaluates.lookup getN) rfl
        · exact BlockReturns.return_value (Evaluates.lookup getN)
      · have tested : Evaluates program env
            (.boolOp .and [.name "n", .compare (.binOp (.name "n") .mod (.name "p")) [(.eq, .constant (.int 0))]])
            (.bool (decide (n % p = 0))) := by
          apply Evaluates.boolean_continue (Evaluates.lookup getN)
            (by simp [scalarTruth, zero])
          apply Evaluates.boolean_last
          apply Evaluates.compare (av := .int (n % p)) (Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup getP)
            (by simp [scalarBinary, show p ≠ 0 by omega, show 0 < p by omega])) Evaluates.constant
          simp [scalarCompare, evalCmpOp, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
        by_cases divisible : n % p = 0
        · have result : stripFactor p n = stripFactor p (n / p) := by
            rw [stripFactor]; simp [show ¬p ≤ 1 by omega, zero, divisible]
          rw [result]
          apply BlockReturns.while_loop (value := .bool true) (by simpa [divisible] using tested)
          apply BlockReturns.augAssign (value := .int (n / p))
          · exact Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup getP)
              (by simp [scalarBinary, show p ≠ 0 by omega, show 0 < p by omega])
          · apply ih (n / p) (Nat.div_lt_self (by omega) large)
            all_goals simp [ScalarEnv.set, getP]
        · have result : stripFactor p n = n := by
            rw [stripFactor]; simp [show ¬p ≤ 1 by omega, zero, divisible]
          rw [result]
          apply BlockReturns.while_loop (value := .bool false) (by simpa [divisible] using tested)
          exact BlockReturns.return_value (Evaluates.lookup getN)

theorem strip_factor.result (p n : Nat) :
    ReturnsValue program "strip_factor" [.int p, .int n] (.int (stripFactor p n)) := by
  apply BlockReturns.function rfl rfl
  by_cases small : p ≤ 1
  · have result : stripFactor p n = n := by rw [stripFactor]; simp [small]
    rw [result]
    apply BlockReturns.branch (value := .bool true)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp, small]))
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · apply BlockReturns.branch (value := .bool false)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp, small]))
    exact strip_loop p n (by omega) _ rfl rfl

theorem reduced_denom.result (n : Nat) :
    ReturnsValue program "reduced_denom" [.int n] (.int (reducedDenom n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons Evaluates.constant (.cons
    (Evaluates.call (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil))
      (strip_factor.result 2 n)) .nil)) (strip_factor.result 5 (stripFactor 2 n))

private def cycleBody : List Stmt :=
  [.ifThen (.compare (.name "r") [(.eq, .constant (.int 1))]) [.return (.name "k")] [],
   .assign [.name "r"] (.binOp (.binOp (.name "r") .mult (.constant (.int 10))) .mod (.name "d")),
   .augAssign (.name "k") .add (.constant (.int 1))]

private theorem cycle_loop (steps start d r k : Nat) (positive : 0 < d) (env : ScalarEnv)
    (getD : env "d" = some (.int d)) (getR : env "r" = some (.int r)) (getK : env "k" = some (.int k)) :
    BlockReturns program env
      [.rangeStepLoop "_" start (start + steps) 1 cycleBody [], .return (.constant (.int 0))]
      (.int (cycleLenAux.go d r k steps)) := by
  induction steps generalizing start r k env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues])
      exact BlockReturns.return_value Evaluates.constant
  | succ steps ih =>
      rw [cycleLenAux.go]
      apply BlockReturns.range_step (by simp [rangeContinues])
      by_cases hit : r = 1
      · rw [if_pos hit]
        apply BlockReturns.branch (value := .bool true)
          (Evaluates.compare (Evaluates.lookup (value := .int r) (by simp [ScalarEnv.set, getR])) Evaluates.constant
            (by simp [scalarCompare, evalCmpOp, hit]))
        exact BlockReturns.return_value (Evaluates.lookup (value := .int k) (by simp [ScalarEnv.set, getK]))
      · rw [if_neg hit]
        apply BlockReturns.branch (value := .bool false)
          (Evaluates.compare (Evaluates.lookup (value := .int r) (by simp [ScalarEnv.set, getR])) Evaluates.constant
            (by simp [scalarCompare, evalCmpOp, hit]))
        apply BlockReturns.assign (value := .int ((r * 10) % d))
        · apply Evaluates.binary (av := .int (r * 10))
            (Evaluates.binary (Evaluates.lookup (value := .int r) (by simp [ScalarEnv.set, getR])) Evaluates.constant
              (by simp [scalarBinary])) (Evaluates.lookup (value := .int d) (by simp [ScalarEnv.set, getD]))
          simp [scalarBinary, show d ≠ 0 by omega, positive]
        · apply BlockReturns.augAssign (value := .int (k + 1))
          · exact Evaluates.binary (Evaluates.lookup (value := .int k) (by simp [ScalarEnv.set, getK])) Evaluates.constant
              (by simp [scalarBinary])
          · have run := ih (start + 1) ((r * 10) % d) (k + 1)
              (((env.set "_" (.int start)).set "r" (.int ((r * 10) % d))).set "k" (.int (k + 1)))
              (by simp [ScalarEnv.set, getD]) (by simp [ScalarEnv.set]) (by simp [ScalarEnv.set])
            simpa only [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm, Int.add_left_comm] using run

theorem cycle_len_aux.result (d : Nat) :
    ReturnsValue program "cycle_len_aux" [.int d] (.int (cycleLenAux d)) := by
  apply BlockReturns.function rfl rfl
  by_cases zero : d = 0
  · subst d
    apply BlockReturns.branch (value := .bool true)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl)
    exact BlockReturns.return_value Evaluates.constant
  · apply BlockReturns.branch (value := .bool false)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp, zero]))
    apply BlockReturns.unpack (names := ["r", "k"]) (results := [.int (10 % d), .int 1]) rfl rfl
    · exact .cons (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) (by simp [scalarBinary, zero, show 0 < d by omega]))
        (.cons Evaluates.constant .nil)
    · apply BlockReturns.for_range (values := [.int d]) (.cons (Evaluates.lookup (by simp [assignNames, ScalarEnv.set, argumentEnv])) .nil) rfl
      simpa [cycleLenAux, zero] using cycle_loop d 0 d (10 % d) 1 (by omega) _
        (by simp [assignNames, ScalarEnv.set, argumentEnv]) (by simp [assignNames, ScalarEnv.set])
        (by simp [assignNames, ScalarEnv.set])

theorem cycle_len.result (d : Nat) :
    ReturnsValue program "cycle_len" [.int d] (.int (cycleLen d)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (reduced_denom.result d))
  apply BlockReturns.return_value
  by_cases terminates : reducedDenom d = 1
  · rw [cycleLen, if_pos terminates]
    apply Evaluates.conditional (c := .bool true)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp, terminates]))
    exact Evaluates.constant
  · rw [cycleLen, if_neg terminates]
    apply Evaluates.conditional (c := .bool false)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp, terminates]))
    exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (cycle_len_aux.result (reducedDenom d))


private theorem scan_result (count start winner : Nat) :
    ExtremumReturns program ⟨true, "cycle_len", start + count, 1⟩ start
      (some (winner, .int (cycleLen winner)))
      (((List.range' start count).foldl (ProjectEulerStatements.ArgMaximum.select cycleLen) winner : Nat) : Int) := by
  induction count generalizing start winner with
  | zero =>
      simpa using ExtremumReturns.done (module := program)
        (range := ⟨true, "cycle_len", start, 1⟩) (next := start)
        (winner := winner) (score := .int (cycleLen winner)) (by simp [rangeContinues])
  | succ count ih =>
      let chosen := ProjectEulerStatements.ArgMaximum.select cycleLen winner start
      simp only [List.range'_succ, List.foldl_cons]
      apply ExtremumReturns.next (score := .int (cycleLen start))
        (updated := (chosen, .int (cycleLen chosen)))
      · simp [rangeContinues]
      · exact cycle_len.result start
      · by_cases better : cycleLen winner < cycleLen start
        all_goals simp [RangeExtremum.choose, scalarCompare, evalCmpOp, chosen,
          ProjectEulerStatements.ArgMaximum.select, better]
      · simpa [Int.natCast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using
          ih (start + 1) chosen

theorem naive.nonpositive (limit : Int) (small : limit ≤ 0) :
    ReturnsValue program "naive" [.int limit] (.int 0) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool false)
    (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp]; omega))
  exact Evaluates.constant

/-- The source's key-based maximum retains the first denominator on equal cycle lengths. -/
theorem naive.result (limit : Nat) :
    ReturnsValue program "naive" [.int limit] (.int (ProjectEulerStatements.P26.naive limit)) := by
  cases limit with
  | zero => exact naive.nonpositive 0 (by omega)
  | succ count =>
      have expected : ProjectEulerStatements.P26.naive (count + 1) =
          (List.range' 1 count).foldl (ProjectEulerStatements.ArgMaximum.select cycleLen) 0 := by
        simp [ProjectEulerStatements.P26.naive, ProjectEulerStatements.ArgMaximum.argmax_range_succ]
      rw [expected]
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      apply Evaluates.conditional (c := .bool true)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp])
      · apply Evaluates.extremum_range (values := [.int (count + 1)])
        · exact .cons (Evaluates.lookup rfl) .nil
        · rfl
        · apply ExtremumReturns.next (score := .int (cycleLen 0)) (updated := (0, .int (cycleLen 0)))
          · simp [rangeContinues]
          · exact cycle_len.result 0
          · rfl
          · simpa [Int.add_comm] using scan_result count 1 0

theorem naive.«Returns» (limit : Int) : (Calls.function program "naive" [.int limit]).Returns := by
  by_cases nonnegative : 0 ≤ limit
  · lift limit to Nat using nonnegative
    exact (naive.result limit).returns
  · exact (naive.nonpositive limit (by omega)).returns

theorem naive.«Supported» (limit : Int) : (Calls.function program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p26
