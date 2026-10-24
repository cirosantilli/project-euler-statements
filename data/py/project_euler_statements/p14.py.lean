import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p14.py.ast»
import FormalSW
import ProjectEulerStatements.Lib.Collatz
import ProjectEulerStatements.Lib.ArgMaximum

namespace data.«project-euler-statements».data.py.project_euler_statements.p14
open FormalSW.PyAst
private abbrev program := P14Ast.module
section
open Calls

theorem collatz_step.result (n : Int) :
    ReturnsValue program "collatz_step" [.int n]
      (.int (ProjectEulerStatements.Collatz.stepInt n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have condition : Evaluates program (argumentEnv [{ name := "n", annotation := some (.name "int") }] [.int n])
      (.compare (.binOp (.name "n") .mod (.constant (.int 2))) [(.eq, .constant (.int 0))])
      (.bool (decide (n % 2 = 0))) := by
    apply Evaluates.compare (av := .int (n % 2)) (bv := .int 0)
    · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])
    · exact Evaluates.constant
    · simp [scalarCompare, evalCmpOp]
  by_cases even : n % 2 = 0
  · simp only [ProjectEulerStatements.Collatz.stepInt, even, ↓reduceIte]
    apply Evaluates.conditional (c := .bool true) (by simpa [even] using condition)
    exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])
  · simp only [ProjectEulerStatements.Collatz.stepInt, even, ↓reduceIte]
    apply Evaluates.conditional (c := .bool false) (by simpa [even] using condition)
    apply Evaluates.binary
      (Evaluates.binary (value := .int (3 * n)) Evaluates.constant (Evaluates.lookup rfl)
        (by simp [scalarBinary])) Evaluates.constant
    simp [scalarBinary]

theorem collatz_step.«Returns» (n : Int) :
    (function program "collatz_step" [.int n]).Returns :=
  (collatz_step.result n).returns


end

namespace Cached
open MemoCalls ProjectEulerStatements.P14

private def cacheSpec (key : Key) (value : Constant) : Prop :=
  ∃ n : Nat, key = ⟨"collatz_len", [n]⟩ ∧ value = .int (collatzLen n)

private theorem step_result (n : Int) :
    ReturnsValue program ["collatz_len"] cacheSpec "collatz_step" [.int n]
      (.int (ProjectEulerStatements.Collatz.stepInt n)) := by
  apply BlockReturns.function (by decide) rfl rfl
  apply BlockReturns.return_value
  have condition : Evaluates program ["collatz_len"] cacheSpec (argumentEnv [{ name := "n", annotation := some (.name "int") }] [.int n])
      (.compare (.binOp (.name "n") .mod (.constant (.int 2))) [(.eq, .constant (.int 0))])
      (.bool (decide (n % 2 = 0))) := by
    apply Evaluates.compare (av := .int (n % 2)) (bv := .int 0)
    · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])
    · exact Evaluates.constant
    · simp [scalarCompare, evalCmpOp]
  by_cases even : n % 2 = 0
  · simp only [ProjectEulerStatements.Collatz.stepInt, even, ↓reduceIte]
    apply Evaluates.conditional (c := .bool true) (by simpa [even] using condition)
    exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])
  · simp only [ProjectEulerStatements.Collatz.stepInt, even, ↓reduceIte]
    apply Evaluates.conditional (c := .bool false) (by simpa [even] using condition)
    apply Evaluates.binary
      (Evaluates.binary (value := .int (3 * n)) Evaluates.constant (Evaluates.lookup rfl)
        (by simp [scalarBinary])) Evaluates.constant
    simp [scalarBinary]


theorem length_result (n : Nat) :
    ReturnsValue program ["collatz_len"] cacheSpec "collatz_len" [.int n] (.int (collatzLen n)) := by
  induction h : collatzMeasure n using Nat.strong_induction_on generalizing n with
  | h measure ih =>
      apply BlockReturns.memoized_function (values := [n]) (by simp) rfl rfl
      · by_cases zero : n = 0
        · subst n
          simp only [ProjectEulerStatements.Collatz.length_zero]
          apply BlockReturns.branch (value := .bool true)
          · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
          · exact BlockReturns.return_value Evaluates.constant
        · apply BlockReturns.branch (value := .bool false)
          · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
              (by simp [scalarCompare, evalCmpOp, zero])
          · by_cases one : n = 1
            · subst n
              simp only [ProjectEulerStatements.Collatz.length_one]
              apply BlockReturns.branch (value := .bool true)
              · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
              · exact BlockReturns.return_value Evaluates.constant
            · apply BlockReturns.branch (value := .bool false)
              · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
                  (by simp [scalarCompare, evalCmpOp]; omega)
              · apply BlockReturns.return_value
                apply Evaluates.binary (av := .int 1) (bv := .int (collatzLen (collatzStep n)))
                · exact Evaluates.constant
                · apply Evaluates.call (values := [.int (collatzStep n)])
                  · apply Evaluates.Arguments.cons _ .nil
                    simpa [ProjectEulerStatements.Collatz.stepInt_nat] using
                      Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (step_result n)
                  · apply ih (collatzMeasure (collatzStep n)) _ (collatzStep n) rfl
                    rw [← h]
                    exact collatzMeasure_decreases (by omega) one
                · rw [ProjectEulerStatements.Collatz.length_step n (by omega) one]
                  simp [scalarBinary, Int.add_comm]
      · exact ⟨n, rfl, rfl⟩
      · rintro other ⟨k, same, rfl⟩
        have equalInt : (n : Int) = k := by simpa [Key.mk.injEq] using same
        have equal : n = k := by omega
        simp [equal]


private theorem scan_result (count start winner : Nat) :
    ExtremumReturns program ["collatz_len"] cacheSpec
      ⟨true, "collatz_len", start + count, 1⟩ start
      (some (winner, .int (collatzLen winner)))
      (((List.range' start count).foldl (ProjectEulerStatements.ArgMaximum.select collatzLen) winner : Nat) : Int) := by
  induction count generalizing start winner with
  | zero =>
      simpa using ExtremumReturns.done (module := program) (memoized := ["collatz_len"])
        (spec := cacheSpec) (range := ⟨true, "collatz_len", start, 1⟩)
        (current := start) (winner := winner) (score := .int (collatzLen winner))
        (by simp [Calls.rangeContinues])
  | succ count ih =>
      let chosen := ProjectEulerStatements.ArgMaximum.select collatzLen winner start
      simp only [List.range'_succ, List.foldl_cons]
      apply ExtremumReturns.next (score := .int (collatzLen start))
        (updated := (chosen, .int (collatzLen chosen)))
      · simp [Calls.rangeContinues]
        omega
      · exact length_result start
      · by_cases better : collatzLen winner < collatzLen start
        all_goals simp [Calls.RangeExtremum.choose, scalarCompare, evalCmpOp, chosen,
          ProjectEulerStatements.ArgMaximum.select, better]
      · simpa [Int.natCast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using
          ih (start + 1) chosen

theorem naive_result (n : Nat) :
    ReturnsValue program ["collatz_len"] cacheSpec "naive" [.int n]
      (.int (ProjectEulerStatements.P14.naive n)) := by
  have expected : ProjectEulerStatements.P14.naive n =
      (List.range' 1 n).foldl (ProjectEulerStatements.ArgMaximum.select collatzLen) 0 := by
    simp [ProjectEulerStatements.P14.naive, ProjectEulerStatements.ArgMaximum.argmax_range_succ]
  rw [expected]
  apply BlockReturns.function (by simp) rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool true)
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp])
  · apply Evaluates.extremum_range (values := [.int (n + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil
    · rfl
    · apply ExtremumReturns.next (score := .int (collatzLen 0)) (updated := (0, .int (collatzLen 0)))
      · simp [Calls.rangeContinues]
      · exact length_result 0
      · rfl
      · simpa [Int.add_comm] using scan_result n 1 0

theorem naive_negative (n : Int) (negative : n < 0) :
    ReturnsValue program ["collatz_len"] cacheSpec "naive" [.int n] (.int 0) := by
  apply BlockReturns.function (by simp) rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool false)
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarCompare, evalCmpOp]; omega)
  · exact Evaluates.constant

end Cached

theorem collatz_len.«Returns» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) P14Ast.requires_collatz_len_0) :
    (MemoCalls.sourceFunction program "collatz_len" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
  simpa [MemoCalls.sourceFunction, Int.toNat_of_nonneg nonnegative] using
    (Cached.length_result n.toNat).returns

theorem collatz_len.«Supported» (n : Int) (hp : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) P14Ast.requires_collatz_len_0) :
    (MemoCalls.sourceFunction program "collatz_len" [.int n]).Supported :=
  (collatz_len.«Returns» n hp).supported

theorem naive.«Returns» (limit : Int) :
    (MemoCalls.sourceFunction program "naive" [.int limit]).Returns := by
  by_cases nonnegative : 0 ≤ limit
  · simpa [MemoCalls.sourceFunction, Int.toNat_of_nonneg nonnegative] using
      (Cached.naive_result limit.toNat).returns
  · exact (Cached.naive_negative limit (by omega)).returns

theorem naive.«Supported» (limit : Int) :
    (MemoCalls.sourceFunction program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p14
