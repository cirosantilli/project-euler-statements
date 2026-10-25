import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p70.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P69

namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst Calls
set_option Elab.async false

abbrev program := P70Ast.module
abbrev gcdCondition : Expr := .compare (.call (.name "gcd") [.name "k", .name "n"])
  [(.eq, .constant (.int 1))]

private def coprimeCount (n first : Nat) : Nat :=
  ((Finset.Icc first n).filter (fun k => Nat.gcd k n = 1)).card

private theorem count_done (n first : Nat) (finished : n < first) : coprimeCount n first = 0 := by
  simp [coprimeCount, Finset.Icc_eq_empty_of_lt finished]

private theorem count_step (n first : Nat) (active : first ≤ n) :
    coprimeCount n first =
      (if Nat.gcd first n = 1 then 1 else 0) + coprimeCount n (first + 1) := by
  have interval : Finset.Icc first n = insert first (Finset.Icc (first + 1) n) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold coprimeCount
  rw [interval]
  by_cases chosen : Nat.gcd first n = 1
  · simp [Finset.filter_insert, chosen, Finset.mem_filter, Finset.mem_Icc, Nat.add_comm]
  · simp [Finset.filter_insert, chosen]

theorem gcd_condition_result (n k : Nat) (env : ScalarEnv)
    (getN : env "n" = some (.int n)) (getK : env "k" = some (.int k)) :
    Evaluates program env (.boolOp .and [gcdCondition])
      (.bool (decide (Nat.gcd k n = 1))) := by
  apply Evaluates.boolean_last
  apply Evaluates.compare (av := .int (Nat.gcd k n)) (bv := .int 1)
  · apply Evaluates.library_call
      (.cons (Evaluates.lookup getK) (.cons (Evaluates.lookup getN) .nil)) rfl
    change some (Math.gcdCall [.int k, .int n]) = _
    simpa using congrArg some (Math.gcdCall_pair (k : Int) (n : Int))
  · exact Evaluates.constant
  · simp [scalarCompare, evalCmpOp]

private theorem count_loop (n first total : Nat) (env : ScalarEnv)
    (getN : env "n" = some (.int n)) :
    SumReturns program ⟨"k", .constant (.int 1), [gcdCondition], (n : Int) + 1, 1, env⟩
      first total (total + coprimeCount n first) := by
  by_cases active : first ≤ n
  · have tested := gcd_condition_result n first (env.set "k" (.int first))
      (by simpa [ScalarEnv.set] using getN) (by simp [ScalarEnv.set])
    by_cases chosen : Nat.gcd first n = 1
    · apply SumReturns.keep (by simp [rangeContinues]; omega)
        (by simpa only [chosen, decide_true] using tested) rfl (item := .int 1)
        (updated := (total : Int) + 1) Evaluates.constant rfl
      have continued := count_loop n (first + 1) (total + 1) env getN
      simpa only [count_step n first active, chosen, if_true, Nat.cast_add,
        Nat.cast_one, Int.add_assoc] using continued
    · apply SumReturns.skip (by simp [rangeContinues]; omega)
        (by simpa only [chosen, decide_false] using tested) rfl
      have continued := count_loop n (first + 1) total env getN
      simpa only [count_step n first active, chosen, if_false, Nat.zero_add,
        Nat.cast_add, Nat.cast_one] using continued
  · have empty := count_done n first (by omega)
    simpa only [empty, Nat.add_zero] using
      (SumReturns.done (module := program)
        (sum := ⟨"k", .constant (.int 1), [gcdCondition], (n : Int) + 1, 1, env⟩)
        (next := first) (total := total) (by simp [rangeContinues]; omega))
termination_by n + 1 - first
decreasing_by all_goals omega

theorem phi.natural_result (n : Nat) : ReturnsValue program "phi" [.int n] (.int n.totient) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
    (.cons Evaluates.constant (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)) rfl
  have count : coprimeCount n 1 = n.totient := ProjectEulerStatements.P69.phi_eq_totient n
  simpa only [Nat.cast_zero, Nat.cast_one, Int.zero_add, count] using
    count_loop n 1 0 (argumentEnv [⟨"n", some (.name "int"), none⟩] [.int n]) rfl

theorem phi.result (n : Int) : ReturnsValue program "phi" [.int n] (.int n.toNat.totient) := by
  by_cases negative : n < 0
  · have clipped : n.toNat = 0 := by omega
    rw [clipped, Nat.totient_zero]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
      (.cons Evaluates.constant (.cons
        (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)) rfl
    exact SumReturns.done (by simp [rangeContinues]; omega)
  · have cast : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
    simpa only [cast] using phi.natural_result n.toNat

end data.«project-euler-statements».data.py.project_euler_statements.p70
