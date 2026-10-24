import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p15.py.ast»
import FormalSW
import ProjectEulerStatements.P15
import ProjectEulerStatements.Lib.Binomial

namespace data.«project-euler-statements».data.py.project_euler_statements.p15
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := P15Ast.module

/-- Connect the standard-library execution model to the reusable binomial theorem. -/
theorem comb_eq_choose (n k : Nat) : Math.comb n k = Nat.choose n k := by
  unfold Math.comb
  split_ifs with large
  · exact (Nat.choose_eq_zero_of_lt large).symm
  · have bound : min k (n - k) ≤ n := by omega
    rw [ProjectEulerStatements.Binomial.recurrence_eq
      (n - min k (n - k)) (Math.combProduct (n - min k (n - k))) rfl (fun _ => rfl),
      Nat.sub_add_cancel bound, ProjectEulerStatements.Binomial.choose_min n k (by omega)]

theorem naive.result (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P15.naive n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.library_call
    (.cons (Evaluates.binary (value := .int (2 * (n : Int))) Evaluates.constant (Evaluates.lookup rfl) (by simp [scalarBinary]))
      (.cons (Evaluates.lookup rfl) .nil)) rfl
  change some (Math.combCall [.int (2 * (n : Int)), .int n]) = _
  rw [show 2 * (n : Int) = ((2 * n : Nat) : Int) by simp, Math.combCall_naturals, comb_eq_choose]
  rfl

theorem naive.«Returns» (n : Int)
    (condition : Condition program (fun name => if name = "n" then some (.int n) else none)
      P15Ast.requires_naive_0) : (function program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare condition rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (naive.result n.toNat).returns

end data.«project-euler-statements».data.py.project_euler_statements.p15
