import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p2.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P2

namespace data.«project-euler-statements».data.py.project_euler_statements.«p2»
open FormalSW.PyAst FormalSW.PyAst.Calls
open ProjectEulerStatements.P2

private abbrev program := P2Ast.module
private def loop : List Stmt :=
  (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2).drop 3

private theorem loop_result (n i total : Nat) (env : ScalarEnv)
    (hn : env "n" = some (.int n)) (ha : env "a" = some (.int (fib i)))
    (hb : env "b" = some (.int (fib (i + 1)))) (ht : env "total" = some (.int total)) :
    BlockReturns program env loop (.int (ProjectEulerStatements.P2.naive.go n (i + 1) total)) := by
  induction h : n - i using Nat.strong_induction_on generalizing i total env with
  | h measure ih =>
      rw [ProjectEulerStatements.P2.naive.go.eq_1]
      apply BlockReturns.while_loop (value := .bool true) Evaluates.constant
      by_cases hle : fib (i + 1) ≤ n
      · simp only [hle, ↓reduceIte]
        have next (t : Nat) (env' : ScalarEnv)
            (hn' : env' "n" = some (.int n)) (ha' : env' "a" = some (.int (fib i)))
            (hb' : env' "b" = some (.int (fib (i + 1))))
            (ht' : env' "total" = some (.int t)) :
            BlockReturns program env'
              (.assign [.tuple [.name "a", .name "b"]]
                (.tuple [.name "b", .binOp (.name "a") .add (.name "b")]) :: loop)
              (.int (ProjectEulerStatements.P2.naive.go n (i + 2) t)) := by
          apply BlockReturns.unpack (names := ["a", "b"])
            (results := [.int (fib (i + 1)), .int (fib (i + 2))]) rfl rfl
          · exact .cons (Evaluates.lookup hb') (.cons
              (Evaluates.binary (Evaluates.lookup ha') (Evaluates.lookup hb')
                (by simp [scalarBinary, fib])) .nil)
          · apply ih (n - (i + 1)) (by have := fib_ge_succ (i + 1); omega)
              (i + 1) t _
            all_goals simp [assignNames, ScalarEnv.set, hn', ht']
        apply BlockReturns.branch (value := .bool false)
        · exact Evaluates.compare (Evaluates.lookup hb) (Evaluates.lookup hn)
            (by simp [scalarCompare, evalCmpOp]; omega)
        · have parity : Evaluates program env
              (.compare (.binOp (.name "b") .mod (.constant (.int 2)))
                [(.eq, .constant (.int 0))]) (.bool (decide (fib (i + 1) % 2 = 0))) := by
            apply Evaluates.compare (av := .int ↑(fib (i + 1) % 2)) (bv := .int 0)
            · exact Evaluates.binary (Evaluates.lookup hb) Evaluates.constant (by simp [scalarBinary])
            · exact Evaluates.constant
            · simp [scalarCompare, evalCmpOp, Int.ofNat_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
          by_cases heven : fib (i + 1) % 2 = 0
          · simp only [heven, ↓reduceIte]
            apply BlockReturns.branch (value := .bool true)
            · simpa [heven] using parity
            · apply BlockReturns.augAssign (value := .int ↑(total + fib (i + 1)))
              · exact Evaluates.binary (Evaluates.lookup ht) (Evaluates.lookup hb)
                  (by simp [scalarBinary])
              · apply next
                all_goals simp [ScalarEnv.set, hn, ha, hb]
          · simp only [heven, ↓reduceIte]
            apply BlockReturns.branch (value := .bool false)
            · simpa [heven] using parity
            · exact next total env hn ha hb ht
      · simp only [hle, ↓reduceIte]
        apply BlockReturns.branch (value := .bool true)
        · exact Evaluates.compare (Evaluates.lookup hb) (Evaluates.lookup hn)
            (by simp [scalarCompare, evalCmpOp]; omega)
        · exact BlockReturns.return_value (Evaluates.lookup ht)

theorem naive.result (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P2.naive.go n 1 0)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.assign Evaluates.constant
  exact loop_result n 0 0 _ rfl rfl rfl rfl

theorem naive.«Returns» (n : Int) (hp : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P2Ast.requires_naive_0) : (Calls.function program "naive" [.int n]).Returns := by
  have hn : n ≥ 0 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg hn] using (naive.result n.toNat).returns

end data.«project-euler-statements».data.py.project_euler_statements.«p2»
