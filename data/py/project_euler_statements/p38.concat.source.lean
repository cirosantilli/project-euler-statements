import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p38.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerStatements.Lib.ConcatenatedProducts
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p38
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.P38
private abbrev program := P38Ast.module
variable {globals : Mutable.Globals}
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number
private abbrev digitHeap (n : Nat) : Mutable.Heap :=
  [.list (numbers (Nat.digits 10 n)), .list (numbers (digitsBE n))]

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 7 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["num_digits", "concat_nat", "concat_product", "is_pandigital",
      "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem digits_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "digits_be" [number n] heap
      (.ref (heap.length + 1)) (heap ++ digitHeap n) := by
  apply ReturnsValue.with_defaults rfl rfl rfl
  simpa [digitHeap, numbers, number, digitsBE, List.map_reverse, List.map_map] using
    (common.digits_be.result (globals := globals) n 10 (by decide) heap).extend common_extension

theorem num_digits.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "num_digits" [number n] heap
      (number (numDigits n)) (heap ++ digitHeap n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
    (digits_result n heap)) .nil)
  simp [primitive, Mutable.length, digitHeap, numbers, digitsBE, numDigits, number]

theorem concat_nat.result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "concat_nat" [number a, number b] heap
      (number (concatNat a b)) (heap ++ digitHeap b) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (a * 10 ^ numDigits b)) (bv := number b)
    (middle := heap ++ digitHeap b) (afterRight := heap ++ digitHeap b)
  · apply Evaluates.binary (av := number a) (bv := number (10 ^ numDigits b))
      (middle := heap) (afterRight := heap ++ digitHeap b) (Evaluates.lookup (by cases globals <;> rfl))
    · apply Evaluates.binary (av := number 10) (bv := number (numDigits b))
        (middle := heap) (afterRight := heap ++ digitHeap b) Evaluates.constant
        (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (num_digits.result b heap))
      simp [Mutable.binary, scalarBinary, number, show ¬ (numDigits b : Int) < 0 by omega]
    · simp [Mutable.binary, scalarBinary, number]
  · exact Evaluates.lookup (by cases globals <;> rfl)
  · simp [Mutable.binary, scalarBinary, number, concatNat]

private abbrev productBody : List Stmt :=
  [.assign [.name "acc"] (.call (.name "concat_nat")
    [.name "acc", .binOp (.name "n") .mult (.binOp (.name "i") .add (.constant (.int 1)))])]

private theorem product_loop (n first count total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getAcc : env "acc" = some (number total)) :
    ∃ extra, BlockReturns (globals := globals) program env
      [.rangeStepLoop "i" first (first + count) 1 productBody [], .return (.name "acc")]
      heap (number ((List.range' first count).foldl (fun acc i => concatNat acc (n * (i + 1))) total))
      (heap ++ extra) := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.range'_zero, List.foldl_nil, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getAcc)
  | succ count ih =>
      let bound := setLocal env "i" (number first)
      let next := concatNat total (n * (first + 1))
      let after := heap ++ digitHeap (n * (first + 1))
      let updated := setLocal bound "acc" (number next)
      obtain ⟨extra, rest⟩ := ih (first + 1) next after updated
        (by simpa [updated, bound, setLocal] using getN) (by simp [updated, setLocal])
      refine ⟨digitHeap (n * (first + 1)) ++ extra, ?_⟩
      simp only [List.range'_succ, List.foldl_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues])
      apply BlockReturns.assign (value := number next) (middle := after)
      · apply Evaluates.call (values := [number total, number (n * (first + 1))])
          (.cons (Evaluates.lookup (by simpa [bound, setLocal] using getAcc)) (.cons
          (Evaluates.binary (av := number n) (bv := number (first + 1))
            (middle := heap) (afterRight := heap) (finalHeap := heap)
            (Evaluates.lookup (by simpa [bound, setLocal] using getN))
            (Evaluates.binary (av := number first) (bv := number 1) (value := number (first + 1))
              (middle := heap) (afterRight := heap) (finalHeap := heap)
              (Evaluates.lookup (by simp [setLocal])) Evaluates.constant
              (by simp [Mutable.binary, scalarBinary, number]))
            (by simp [Mutable.binary, scalarBinary, number])) .nil))
        exact concat_nat.result total (n * (first + 1)) heap
      · simpa [updated, bound, after, next, Nat.add_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm, productBody, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, List.append_assoc] using rest

theorem concat_product.result (n k : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "concat_product" [number n, number k] heap
      (number (concatProduct n k)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "concat_product").getD ([], [])).1
    ((findFunctionIn program.body "concat_product").getD ([], [])).2 [number n, number k] globals
  obtain ⟨extra, loop⟩ := product_loop (globals := globals) n 0 k 0 heap
    (setLocal initial "acc" (number 0)) (by cases globals <;> rfl) (by simp [setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (values := [number k]) (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) rfl
  simpa [initial, productBody, List.range_eq_range', concatProduct] using loop

end data.«project-euler-statements».data.py.project_euler_statements.p38
