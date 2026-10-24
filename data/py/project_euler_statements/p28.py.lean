import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p28.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P28
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p28
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := P28Ast.module
private def layer (k : Nat) : Nat := if k = 0 then 1 else ProjectEulerStatements.P28.layerSum k
private def element : Expr := .ifExp (.compare (.name "k") [(.eq, .constant (.int 0))])
  (.constant (.int 1)) (.call (.name "layer_sum") [.name "k"])

theorem layer_sum.result (k : Nat) :
    ReturnsValue program "layer_sum" [.int k] (.int (ProjectEulerStatements.P28.layerSum k)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (bv := .int 4)
  · apply Evaluates.binary (av := .int (16 * (k : Int) ^ 2)) (bv := .int (4 * k))
    · exact Evaluates.binary Evaluates.constant
        (Evaluates.binary (value := .int ((k : Int) ^ 2)) (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) rfl
    · exact Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl
    · rfl
  · exact Evaluates.constant
  · simp [scalarBinary, ProjectEulerStatements.P28.layerSum]

private theorem element_result (k : Nat) (env : ScalarEnv) (lookup : env "k" = some (.int k)) :
    Evaluates program env element (.int (layer k)) := by
  apply Evaluates.conditional (c := .bool (decide (k = 0)))
  · exact Evaluates.compare (Evaluates.lookup lookup) Evaluates.constant
      (by simp [scalarCompare, evalCmpOp])
  · by_cases zero : k = 0
    · subst k
      exact Evaluates.constant
    · simpa [scalarTruth, layer, zero] using
        Evaluates.call (.cons (Evaluates.lookup lookup) .nil) (layer_sum.result k)

private theorem sum_result (start count total : Nat) (env : ScalarEnv) :
    SumReturns program ⟨"k", element, [], start + count, 1, env⟩ start total
      (((List.range' start count).foldl (fun total k => total + layer k) total : Nat) : Int) := by
  induction count generalizing start total with
  | zero =>
      simp only [List.range'_zero, List.foldl_nil, Nat.cast_zero, add_zero]
      exact SumReturns.done (by simp [rangeContinues])
  | succ count ih =>
      rw [List.range'_succ, List.foldl_cons]
      apply SumReturns.keep (value := .bool true) (item := .int (layer start))
        (updated := (total + layer start : Nat))
      · simp [rangeContinues]
      · exact Evaluates.constant
      · rfl
      · exact element_result start _ (by simp [ScalarEnv.set])
      · simp [sumAdd]
      · simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, add_assoc, add_comm, add_left_comm] using ih (start + 1) (total + layer start)

theorem spiral_diag_sum.result (n : Int) :
    ReturnsValue program "spiral_diag_sum" [.int n]
      (.int (((List.range (((n - 1) / 2 + 1).toNat)).foldl
        (fun total k => total + layer k) 0 : Nat) : Int)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .int ((n - 1) / 2))
  · exact Evaluates.binary
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) Evaluates.constant rfl
  · apply BlockReturns.return_value
    apply Evaluates.sum_range (values := [.int ((n - 1) / 2 + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil
    · rfl
    · by_cases positive : 0 ≤ (n - 1) / 2 + 1
      · have cast := Int.toNat_of_nonneg positive
        simpa [cast, List.range_eq_range'] using
          sum_result 0 (((n - 1) / 2 + 1).toNat) 0
            (ScalarEnv.set (argumentEnv [{ name := "n", annotation := some (.name "int") }] [.int n]) "layers" (.int ((n - 1) / 2)))
      · have empty : ((n - 1) / 2 + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
        simp only [empty, List.range_zero, List.foldl_nil, Nat.cast_zero]
        exact SumReturns.done (by simp [rangeContinues]; omega)

theorem naive.result (n : Nat) (positive : 1 ≤ n) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P28.naive n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have bound : (((n : Int) - 1) / 2 + 1).toNat = (n - 1) / 2 + 1 := by
    have difference : (n : Int) - 1 = ((n - 1 : Nat) : Int) := by omega
    rw [difference]
    norm_cast
  have result := spiral_diag_sum.result n
  rw [bound] at result
  have same : (fun (total k : Nat) => total + layer k) =
      (fun total k => if k = 0 then total + 1 else total + ProjectEulerStatements.P28.layerSum k) := by
    funext total k
    by_cases zero : k = 0 <;> simp [layer, zero]
  rw [same] at result
  exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) result

theorem naive.«Returns» (n : Int) : (Calls.function program "naive" [.int n]).Returns := by
  apply ReturnsValue.returns
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (spiral_diag_sum.result n))

theorem naive.«Supported» (n : Int) : (Calls.function program "naive" [.int n]).Supported :=
  (naive.«Returns» n).supported

end data.«project-euler-statements».data.py.project_euler_statements.p28
