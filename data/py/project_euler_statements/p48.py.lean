import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p48.py.ast»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.SelfPowers

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p48
open FormalSW.PyAst ProjectEulerSolutions.SelfPowers
private abbrev program := P48Ast.module

private theorem scalar_remainder (a m : Int) (nonzero : m≠0) :
    scalarBinary .mod (.int a) (.int m)=some (.ok (.int (remainder a m))) := by
  by_cases positive : 0<m <;> simp [scalarBinary, nonzero, remainder, positive]

namespace Scalar
open Calls
private abbrev number (n : Int) : Constant := .int n

namespace mod_pow
private abbrev body : List Stmt :=
  [.assign [.name "acc"] (.binOp (.binOp (.name "acc") .mult (.name "a")) .mod (.name "m"))]

private theorem loop (a m : Int) (nonzero : m≠0) (first count stop : Nat) (length : first+count=stop)
    (initial : Int) (env : ScalarEnv) (getA : env "a"=some (number a))
    (getM : env "m"=some (number m)) (getAcc : env "acc"=some (number initial)) :
    BlockReturns program env [.rangeStepLoop "_" first stop 1 body [], .return (.name "acc")]
      (number (multiplyLoop a m count initial)) := by
  induction count generalizing first initial env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getAcc)
  | succ count ih =>
      rw [multiplyLoop]
      let bound := env.set "_" (number first)
      have boundA : bound "a"=some (number a) := by simpa [bound, ScalarEnv.set] using getA
      have boundM : bound "m"=some (number m) := by simpa [bound, ScalarEnv.set] using getM
      have boundAcc : bound "acc"=some (number initial) := by simpa [bound, ScalarEnv.set] using getAcc
      have updated : Evaluates program bound
          (.binOp (.binOp (.name "acc") .mult (.name "a")) .mod (.name "m"))
          (number (remainder (initial*a) m)) := by
        apply Evaluates.binary (av := number (initial*a)) (bv := number m)
        · exact Evaluates.binary (Evaluates.lookup boundAcc) (Evaluates.lookup boundA) rfl
        · exact Evaluates.lookup boundM
        · exact scalar_remainder (initial*a) m nonzero
      apply BlockReturns.range_step (by simp [rangeContinues]; omega)
      apply BlockReturns.assign updated
      have rest := ih (first+1) (by omega) (remainder (initial*a) m) (bound.set "acc" (number (remainder (initial*a) m)))
        (by simpa [ScalarEnv.set] using boundA) (by simpa [ScalarEnv.set] using boundM) (by simp [ScalarEnv.set])
      simpa [body, loopContinuation, loopControl, loopControlStmt, Int.natCast_add] using rest

/-- Repeated multiplication terminates for every integer exponent and nonzero signed modulus. -/
theorem result (a b m : Int) (nonzero : m≠0) :
    ReturnsValue program "mod_pow" [number a, number b, number m] (number (power a b m)) := by
  let entry := argumentEnv ((findFunctionIn program.body "mod_pow").getD ([], [])).1 [number a, number b, number m]
  let initialized := entry.set "acc" (number 1)
  let ready := initialized.set "a" (number (remainder a m))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.augAssign (value := number (remainder a m))
    (Evaluates.binary (Evaluates.lookup rfl)
      (Evaluates.lookup rfl) (scalar_remainder a m nonzero))
  apply BlockReturns.for_range (.cons (Evaluates.lookup rfl) .nil) rfl
  by_cases below : b<0
  · have empty : b.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    simp only [power, empty, multiplyLoop]
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · lift b to Nat using (by omega : 0≤b)
    have run := loop (remainder a m) m nonzero 0 b b (by omega) 1 ready
      (by simp [ready, ScalarEnv.set]) rfl
      (by simp [ready, initialized, ScalarEnv.set])
    simpa only [power, Int.toNat_natCast] using run
end mod_pow

namespace series_mod
private abbrev body : List Stmt := [.assign [.name "acc"]
  (.binOp (.binOp (.name "acc") .add (.call (.name "mod_pow")
    [.binOp (.name "i") .add (.constant (.int 1)), .binOp (.name "i") .add (.constant (.int 1)), .name "m"])) .mod (.name "m"))]

private theorem loop (m : Int) (nonzero : m≠0) (first count stop : Nat) (length : first+count=stop)
    (initial : Int) (env : ScalarEnv) (getM : env "m"=some (number m)) (getAcc : env "acc"=some (number initial)) :
    BlockReturns program env [.rangeStepLoop "i" first stop 1 body [], .return (.name "acc")]
      (number (series first count m initial)) := by
  induction count generalizing first initial env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getAcc)
  | succ count ih =>
      rw [series_succ]
      let bound := env.set "i" (number first)
      have boundM : bound "m"=some (number m) := by simpa [bound, ScalarEnv.set] using getM
      have boundAcc : bound "acc"=some (number initial) := by simpa [bound, ScalarEnv.set] using getAcc
      have next : Evaluates program bound (.binOp (.name "i") .add (.constant (.int 1))) (number ((first+1 : Nat) : Int)) :=
        Evaluates.binary (av := number first) (bv := number 1) (Evaluates.lookup (by simp [bound, ScalarEnv.set])) Evaluates.constant (by simp [scalarBinary, number])
      have term : Evaluates program bound (.call (.name "mod_pow")
          [.binOp (.name "i") .add (.constant (.int 1)), .binOp (.name "i") .add (.constant (.int 1)), .name "m"])
          (number (selfPower first m)) :=
        Evaluates.call (.cons next (.cons next (.cons (Evaluates.lookup boundM) .nil)))
          (mod_pow.result ((first+1 : Nat) : Int) ((first+1 : Nat) : Int) m nonzero)
      apply BlockReturns.range_step (by simp [rangeContinues]; omega)
      apply BlockReturns.assign (value := number (remainder (initial+selfPower first m) m))
      · exact Evaluates.binary (Evaluates.binary (Evaluates.lookup boundAcc) term rfl) (Evaluates.lookup boundM)
          (scalar_remainder (initial+selfPower first m) m nonzero)
      · have rest := ih (first+1) (by omega) (remainder (initial+selfPower first m) m)
          (bound.set "acc" (number (remainder (initial+selfPower first m) m)))
          (by simpa [ScalarEnv.set] using boundM) (by simp [ScalarEnv.set])
        simpa [body, loopContinuation, loopControl, loopControlStmt, Int.natCast_add] using rest

/-- The finite reference series preserves exact signed remainder semantics, including empty ranges. -/
theorem result (n m : Int) (nonzero : m≠0) :
    ReturnsValue program "series_mod" [number n, number m] (number (series 0 n.toNat m 0)) := by
  let initial := argumentEnv ((findFunctionIn program.body "series_mod").getD ([], [])).1 [number n, number m]
  let ready := initial.set "acc" (number 0)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (.cons (Evaluates.lookup rfl) .nil) rfl
  by_cases below : n<0
  · have empty : n.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    rw [empty, series_zero]
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · lift n to Nat using (by omega : 0≤n)
    simpa only [Int.toNat_natCast] using loop m nonzero 0 n n (by omega) 0 ready
      rfl (by simp [ready, ScalarEnv.set])
end series_mod
end Scalar

private abbrev modEnv (m : Int) : ScalarEnv := fun name => if name="m" then some (.int m) else none

theorem mod_pow.«Returns» (a b m : Int) (condition : Calls.Condition program (modEnv m) P48Ast.requires_mod_pow_0) :
    (Calls.function program "mod_pow" [.int a, .int b, .int m]).Returns := by
  have nonzero : m≠0 := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  exact (Scalar.mod_pow.result a b m nonzero).returns

theorem series_mod.«Returns» (n m : Int) (condition : Calls.Condition program (modEnv m) P48Ast.requires_series_mod_0) :
    (Calls.function program "series_mod" [.int n, .int m]).Returns := by
  have nonzero : m≠0 := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  exact (Scalar.series_mod.result n m nonzero).returns

namespace naive
open Calls

theorem result (n : Int) : ReturnsValue program "naive" [.int n] (.int (series 0 n.toNat (10^10) 0)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call (.cons (Evaluates.lookup rfl) (.cons
    (Evaluates.binary (av := .int 10) (bv := .int 10) Evaluates.constant Evaluates.constant rfl) .nil))
  exact Scalar.series_mod.result n (10^10) (by decide)

theorem «Returns» (n : Int) : (Calls.function program "naive" [.int n]).Returns := (result n).returns

theorem «Supported» (n : Int) : (Calls.function program "naive" [.int n]).Supported := («Returns» n).supported
end naive

namespace Heap
open HeapCalls
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

private theorem remainder_result (a m : Int) (nonzero : m≠0) (heap : Mutable.Heap) :
    Mutable.binary .mod (number a) (number m) heap=some (.ok (number (remainder a m)), heap) := by
  simp [Mutable.binary, scalar_remainder a m nonzero]

namespace mod_pow
private abbrev body : List Stmt := Scalar.mod_pow.body

private theorem loop (a m : Int) (nonzero : m≠0) (first count stop : Nat) (length : first+count=stop)
    (initial : Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (getA : env "a"=some (number a))
    (getM : env "m"=some (number m)) (getAcc : env "acc"=some (number initial)) :
    BlockReturns program env [.rangeStepLoop "_" first stop 1 body [], .return (.name "acc")]
      heap (number (multiplyLoop a m count initial)) heap := by
  induction count generalizing first initial env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getAcc)
  | succ count ih =>
      rw [multiplyLoop]
      let bound := setLocal env "_" (number first)
      have boundA : bound "a"=some (number a) := by simpa [bound, setLocal] using getA
      have boundM : bound "m"=some (number m) := by simpa [bound, setLocal] using getM
      have boundAcc : bound "acc"=some (number initial) := by simpa [bound, setLocal] using getAcc
      have updated : Evaluates program bound
          (.binOp (.binOp (.name "acc") .mult (.name "a")) .mod (.name "m"))
          heap (number (remainder (initial*a) m)) heap := by
        apply Evaluates.binary (av := number (initial*a)) (bv := number m) (middle := heap) (afterRight := heap)
        · exact Evaluates.binary (av := number initial) (bv := number a) (middle := heap) (afterRight := heap)
            (Evaluates.lookup boundAcc) (Evaluates.lookup boundA) rfl
        · exact Evaluates.lookup boundM
        · exact remainder_result (initial*a) m nonzero heap
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      apply BlockReturns.assign updated
      have rest := ih (first+1) (by omega) (remainder (initial*a) m)
        (setLocal bound "acc" (number (remainder (initial*a) m)))
        (by simpa [setLocal] using boundA) (by simpa [setLocal] using boundM) (by simp [setLocal])
      simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Int.natCast_add] using rest

/-- The heap interpreter executes the same reference multiplication loop without allocations. -/
theorem result (a b m : Int) (nonzero : m≠0) (heap : Mutable.Heap) :
    ReturnsValue program "mod_pow" [number a, number b, number m] heap (number (power a b m)) heap := by
  let entry := functionEnv ((findFunctionIn program.body "mod_pow").getD ([], [])).1
    ((findFunctionIn program.body "mod_pow").getD ([], [])).2 [number a, number b, number m] []
  let initialized := setLocal entry "acc" (number 1)
  let ready := setLocal initialized "a" (number (remainder a m))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.augAssign (value := number (remainder a m)) (middle := heap) (afterOperation := heap)
    rfl (Evaluates.lookup rfl)
  · simpa only [inplace] using remainder_result a m nonzero heap
  · apply BlockReturns.for_range (.cons (Evaluates.lookup rfl) .nil) rfl
    by_cases below : b<0
    · have empty : b.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
      simp only [power, empty, multiplyLoop]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup rfl)
    · lift b to Nat using (by omega : 0≤b)
      have run := loop (remainder a m) m nonzero 0 b b (by omega) 1 heap ready rfl rfl rfl
      simpa only [power, Int.toNat_natCast] using run
end mod_pow

namespace series_mod
private abbrev body : List Stmt := Scalar.series_mod.body

private theorem loop (m : Int) (nonzero : m≠0) (first count stop : Nat) (length : first+count=stop)
    (initial : Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (getM : env "m"=some (number m))
    (getAcc : env "acc"=some (number initial)) :
    BlockReturns program env [.rangeStepLoop "i" first stop 1 body [], .return (.name "acc")]
      heap (number (series first count m initial)) heap := by
  induction count generalizing first initial env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getAcc)
  | succ count ih =>
      rw [series_succ]
      let bound := setLocal env "i" (number first)
      have boundM : bound "m"=some (number m) := by simpa [bound, setLocal] using getM
      have boundAcc : bound "acc"=some (number initial) := by simpa [bound, setLocal] using getAcc
      have next : Evaluates program bound (.binOp (.name "i") .add (.constant (.int 1)))
          heap (number ((first+1 : Nat) : Int)) heap :=
        Evaluates.binary (av := number first) (bv := number 1) (middle := heap) (afterRight := heap)
          (Evaluates.lookup (by simp [bound, setLocal])) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
      have term : Evaluates program bound (.call (.name "mod_pow")
          [.binOp (.name "i") .add (.constant (.int 1)), .binOp (.name "i") .add (.constant (.int 1)), .name "m"])
          heap (number (selfPower first m)) heap :=
        Evaluates.call (.cons next (.cons next (.cons (Evaluates.lookup boundM) .nil)))
          (mod_pow.result ((first+1 : Nat) : Int) ((first+1 : Nat) : Int) m nonzero heap)
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      apply BlockReturns.assign (value := number (remainder (initial+selfPower first m) m)) (middle := heap)
      · exact Evaluates.binary (av := number (initial+selfPower first m)) (bv := number m)
          (middle := heap) (afterRight := heap)
          (Evaluates.binary (av := number initial) (bv := number (selfPower first m))
            (middle := heap) (afterRight := heap) (Evaluates.lookup boundAcc) term rfl)
          (Evaluates.lookup boundM) (remainder_result (initial+selfPower first m) m nonzero heap)
      · have rest := ih (first+1) (by omega) (remainder (initial+selfPower first m) m)
          (setLocal bound "acc" (number (remainder (initial+selfPower first m) m)))
          (by simpa [setLocal] using boundM) (by simp [setLocal])
        simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Int.natCast_add] using rest

theorem result (n m : Int) (nonzero : m≠0) (heap : Mutable.Heap) :
    ReturnsValue program "series_mod" [number n, number m] heap (number (series 0 n.toNat m 0)) heap := by
  let entry := functionEnv ((findFunctionIn program.body "series_mod").getD ([], [])).1
    ((findFunctionIn program.body "series_mod").getD ([], [])).2 [number n, number m] []
  let ready := setLocal entry "acc" (number 0)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (.cons (Evaluates.lookup rfl) .nil) rfl
  by_cases below : n<0
  · have empty : n.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    rw [empty, series_zero]
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · lift n to Nat using (by omega : 0≤n)
    simpa only [Int.toNat_natCast] using loop m nonzero 0 n n (by omega) 0 heap ready rfl rfl
end series_mod
end Heap

def decimalModulus (width : Nat) : Nat := 10^width

def digits (n : Int) (width : Nat) : String :=
  Strings.zfill (toString (series 0 n.toNat (decimalModulus width) 0)) width

theorem modulus_positive (width : Nat) : 0<decimalModulus width := Nat.pow_pos (by decide)

namespace naive_digits
open HeapCalls
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

/-- The adapter retains the original modular series and applies Python's str and zfill. -/
theorem result (n : Int) (width : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "naive_digits" [number n, number width] heap (.scalar (.string (digits n width))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.zfill (text := toString (series 0 n.toNat (decimalModulus width) 0))
  · apply Evaluates.builtin (name := .str)
      (.cons (Evaluates.call (values := [number n, number (decimalModulus width)])
        (.cons (Evaluates.lookup rfl) (.cons
          (Evaluates.binary (av := number 10) (bv := number width) (middle := heap) (afterRight := heap) (finalHeap := heap)
            Evaluates.constant (Evaluates.lookup rfl)
            (by simp [Mutable.binary, scalarBinary, number, decimalModulus, show ¬ (width : Int)<0 by omega])) .nil))
        (Heap.series_mod.result n (decimalModulus width) (by have := modulus_positive width; omega) heap)) .nil)
    rfl
  · exact .cons (Evaluates.lookup rfl) .nil
  · rfl
  · intro name impossible
    cases impossible

theorem «Returns» (n width : Int)
    (condition : Calls.Condition program (fun name => if name="k" then some (.int width) else none) P48Ast.requires_naive_digits_0) :
    (HeapCalls.scalarFunction program "naive_digits" [.int n, .int width]).Returns := by
  have nonnegative : 0≤width := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift width to Nat using nonnegative
  exact (result n width []).scalar_returns

theorem «Supported» (n width : Int)
    (condition : Calls.Condition program (fun name => if name="k" then some (.int width) else none) P48Ast.requires_naive_digits_0) :
    (HeapCalls.scalarFunction program "naive_digits" [.int n, .int width]).Supported :=
  («Returns» n width condition).supported
end naive_digits

end data.«project-euler-statements».data.py.project_euler_statements.p48
