import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Search
import lang.py.FormalSW.SequenceArithmeticRelocation

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

abbrev code : List Stmt := executableBody ((findFunctionIn program.body "naive").getD ([], [])).2
def baseHeap (heap : Mutable.Heap) (maxSize : Nat) : Mutable.Heap := heap ++ [.list [number (2 * maxSize + 1)]]
def preparedEnv (env : HeapCalls.Env) (heap : Mutable.Heap) (maxSize : Nat) : HeapCalls.Env :=
  setLocal (setLocal env "limit" (number (2 * maxSize))) "best" (.ref (heap.length + 1))

theorem small_result (maxSize : Int) (small : maxSize < 2) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [integer maxSize] heap (number 0) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true) (middle := heap) (value := .scalar (.bool true))
  · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, small]
  · rfl
  · exact BlockReturns.return_value Evaluates.constant

/-- The source singleton and list repetition allocate the initial sentinel table. -/
theorem allocate_table (maxSize : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getMax : env "k_max" = some (number maxSize))
    (getLimit : env "limit" = some (number (2 * maxSize))) :
    Evaluates program env
      (.binOp (.list [.binOp (.name "limit") .add (.constant (.int 1))]) .mult
        (.binOp (.name "k_max") .add (.constant (.int 1)))) heap (.ref (heap.length + 1))
      (working (baseHeap heap maxSize) (List.replicate (maxSize + 1) (2 * maxSize + 1))) := by
  apply Evaluates.binary (av := .ref heap.length) (bv := number (maxSize + 1))
    (middle := baseHeap heap maxSize) (afterRight := baseHeap heap maxSize)
  · apply Evaluates.list
    exact .cons (Evaluates.binary (av := number (2 * maxSize)) (bv := number 1)
      (Evaluates.lookup getLimit) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])) .nil
  · exact Evaluates.binary (Evaluates.lookup getMax) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])
  · have multiplied := Mutable.Relocation.binary_mult_list_eval (baseHeap heap maxSize) heap.length
      [number (2 * maxSize + 1)] (maxSize + 1) (by simp [baseHeap])
    simpa [Mutable.allocate, baseHeap, working, encode, List.map_replicate, List.append_assoc] using multiplied

/-- Source initialization and the complete recursive DFS produce the exact minima table. -/
theorem prepare (maxSize : Nat) (large : 2 ≤ maxSize) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (getMax : env "k_max" = some (number maxSize)) :
    BlockContinues program env (code.take 4) heap (preparedEnv env heap maxSize)
      (working (baseHeap heap maxSize) (table maxSize)) := by
  let limited := setLocal env "limit" (number (2 * maxSize))
  let ready := preparedEnv env heap maxSize
  have guard : BlockContinues program env [code[0]'(by decide)] heap env heap := by
    apply BlockContinues.branch (flag := false) (middle := heap) (value := .scalar (.bool false))
    · apply Evaluates.compare (Evaluates.lookup getMax) Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, show ¬ (maxSize : Int) < 2 by omega]
    · rfl
    · exact .nil
  have bound : BlockContinues program env [code[1]'(by decide)] heap limited heap := by
    apply BlockContinues.assign
    exact Evaluates.binary Evaluates.constant (Evaluates.lookup getMax) (by simp [Mutable.binary, scalarBinary, number])
  have allocated : BlockContinues program limited [code[2]'(by decide)] heap ready
      (working (baseHeap heap maxSize) (List.replicate (maxSize + 1) (2 * maxSize + 1))) := by
    apply BlockContinues.assign
    exact allocate_table maxSize heap limited (by simpa [limited, setLocal] using getMax) (by simp [limited, setLocal])
  have searched : BlockContinues program ready [code[3]'(by decide)]
      (working (baseHeap heap maxSize) (List.replicate (maxSize + 1) (2 * maxSize + 1))) ready
      (working (baseHeap heap maxSize) (table maxSize)) := by
    apply BlockContinues.discard
    apply Evaluates.call (values := [number 2, number 1, number 0, number 0, number maxSize,
      number (2 * maxSize), .ref (baseHeap heap maxSize).length])
    · exact .cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant
        (.cons (Evaluates.lookup (by simpa [ready, preparedEnv, setLocal] using getMax))
        (.cons (Evaluates.lookup (by simp [ready, preparedEnv, setLocal]))
        (.cons (Evaluates.lookup (by simp [ready, preparedEnv, setLocal, baseHeap])) .nil))))))
    · exact dfs.root maxSize (baseHeap heap maxSize)
  exact guard.append (bound.append (allocated.append searched))

end data.«project-euler-statements».data.py.project_euler_statements.p88.naive
