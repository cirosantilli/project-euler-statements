import data.«project-euler-statements».data.py.project_euler_statements.«p87.py.lean.d».Primes
import ProjectEulerSolutions.Lib.PrimePowerTriples

namespace data.«project-euler-statements».data.py.project_euler_statements.p87
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PrimePowerTriples
set_option Elab.async false

theorem primes_below.complete (limit p : Nat) :
    p ∈ primes_below.values (Nat.sqrt limit + 1) ↔ p ∈ primesThrough (Nat.sqrt limit) := by
  simp [primes_below.values, and_comm]

namespace naive
abbrev code : List Stmt := executableBody ((findFunctionIn program.body "naive").getD ([], [])).2
def inputHeap (heap : Mutable.Heap) (limit : Nat) : Mutable.Heap :=
  heap ++ [.list (numbers ((primes_below.values (Nat.sqrt limit + 1)).map Int.ofNat)), .list []]
def inputEnv (env : HeapCalls.Env) (heap : Mutable.Heap) : HeapCalls.Env :=
  setLocal (setLocal env "ps" (.ref heap.length)) "sums" (.ref (heap.length + 1))

theorem nonpositive_result (limit : Int) (nonpositive : limit ≤ 0) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number limit] heap (number 0) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true) (middle := heap) (value := flag true)
  · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, nonpositive]
  · rfl
  · exact BlockReturns.return_value Evaluates.constant

/-- Source setup preserves the caller heap and allocates the complete prime list and accumulator. -/
theorem prepare (limit : Nat) (positive : 0 < limit) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) :
    BlockContinues program env (code.take 3) heap (inputEnv env heap) (inputHeap heap limit) := by
  let primes := numbers ((primes_below.values (Nat.sqrt limit + 1)).map Int.ofNat)
  let primeHeap := heap ++ [.list primes]
  let primeEnv := setLocal env "ps" (.ref heap.length)
  have first : BlockContinues program env [code[0]'(by decide)] heap env heap := by
    apply BlockContinues.branch (flag := false) (middle := heap) (value := flag false)
    · apply Evaluates.compare (Evaluates.lookup getLimit) Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, positive.ne']
    · rfl
    · exact .nil
  have root : Evaluates program env (.call (.name "isqrt") [.name "limit"]) heap
      (number (Nat.sqrt limit)) heap := by
    apply Evaluates.library_call (.cons (Evaluates.lookup getLimit) .nil) rfl
    change scalarResult (some (Math.isqrtCall [.int limit])) heap = _
    have same : Math.isqrt limit = Nat.sqrt limit := Nat.eq_sqrt.mpr (Math.isqrt_spec _)
    simp [scalarResult, Math.isqrtCall, same, show ¬ (limit : Int) < 0 by omega, number]
  have second : BlockContinues program env [code[1]'(by decide)] heap primeEnv primeHeap := by
    apply BlockContinues.assign
    apply Evaluates.call (middle := heap) (values := [number (Nat.sqrt limit + 1 : Nat)])
    · exact .cons (Evaluates.binary (middle := heap) (afterRight := heap) (av := number (Nat.sqrt limit)) (bv := number 1)
        root Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])) .nil
    · simpa [primeHeap, primes] using primes_below.result (Nat.sqrt limit + 1 : Nat) heap
  have third : BlockContinues program primeEnv [code[2]'(by decide)] primeHeap
      (inputEnv env heap) (inputHeap heap limit) := by
    apply BlockContinues.assign
    simpa [primeHeap, primes, inputHeap, inputEnv, primeEnv, List.append_assoc] using
      (Evaluates.list (module := program) (env := primeEnv) (heap := primeHeap) Evaluates.Arguments.nil)
  exact first.append (second.append third)

abbrev sumExpression : Expr := .binOp
  (.binOp (.binOp (.name "p") .pow (.constant (.int 2))) .add
    (.binOp (.name "q") .pow (.constant (.int 3)))) .add
  (.binOp (.name "r") .pow (.constant (.int 4)))

theorem sum_evaluate (p q r : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getP : env "p" = some (number p)) (getQ : env "q" = some (number q))
    (getR : env "r" = some (number r)) :
    Evaluates program env sumExpression heap (number (p ^ 2 + q ^ 3 + r ^ 4)) heap := by
  apply Evaluates.binary (middle := heap) (afterRight := heap) (av := number (p ^ 2 + q ^ 3)) (bv := number (r ^ 4))
  · exact Evaluates.binary (middle := heap) (afterRight := heap) (av := number (p ^ 2)) (bv := number (q ^ 3))
      (Evaluates.binary (middle := heap) (afterRight := heap) (Evaluates.lookup getP) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
      (Evaluates.binary (middle := heap) (afterRight := heap) (Evaluates.lookup getQ) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
      (by simp [Mutable.binary, scalarBinary, number])
  · exact Evaluates.binary (middle := heap) (afterRight := heap) (Evaluates.lookup getR) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
  · simp [Mutable.binary, scalarBinary, number]

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p87
