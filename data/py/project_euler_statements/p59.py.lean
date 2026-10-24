import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p59.py.ast»
import lang.py.FormalSW.Calls
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.XorDecryption
import Mathlib.Tactic.IntervalCases

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace data.«project-euler-statements».data.py.project_euler_statements.p59
open FormalSW.PyAst
private abbrev program := P59Ast.module

theorem xor.value_eq (a b : Int) : integerBitXor a b = Int.xor a b := by
  cases a <;> cases b <;> rfl

/-- The source XOR helper terminates for both positive and negative integers. -/
theorem xor.result (a b : Int) :
    Calls.ReturnsValue program "xor" [.int a, .int b] (.int (integerBitXor a b)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.binary (Calls.Evaluates.lookup rfl) (Calls.Evaluates.lookup rfl) rfl

theorem xor.«Returns» (a b : Int) :
    (Calls.function program "xor" [.int a, .int b]).Returns :=
  (xor.result a b).returns

/-- Calls from the decryption comprehension preserve every caller heap and global. -/
theorem xor.heap_result (a b : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapCalls.ReturnsValue program "xor" [.scalar (.int a), .scalar (.int b)] heap
      (.scalar (.int (integerBitXor a b))) heap globals := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.binary (av := .scalar (.int a)) (bv := .scalar (.int b))
    (HeapCalls.Evaluates.lookup (by cases globals <;> rfl))
    (HeapCalls.Evaluates.lookup (by cases globals <;> rfl)) rfl

namespace char_weight
private theorem range_00 (value : Nat) (lower : 0 ≤ value) (upper : value < 16)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_01 (value : Nat) (lower : 16 ≤ value) (upper : value < 32)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_02 (value : Nat) (lower : 32 ≤ value) (upper : value < 48)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_03 (value : Nat) (lower : 48 ≤ value) (upper : value < 64)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_04 (value : Nat) (lower : 64 ≤ value) (upper : value < 80)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_05 (value : Nat) (lower : 80 ≤ value) (upper : value < 96)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_06 (value : Nat) (lower : 96 ≤ value) (upper : value < 112)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_07 (value : Nat) (lower : 112 ≤ value) (upper : value < 128)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_08 (value : Nat) (lower : 128 ≤ value) (upper : value < 144)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_09 (value : Nat) (lower : 144 ≤ value) (upper : value < 160)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_10 (value : Nat) (lower : 160 ≤ value) (upper : value < 176)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_11 (value : Nat) (lower : 176 ≤ value) (upper : value < 192)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_12 (value : Nat) (lower : 192 ≤ value) (upper : value < 208)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_13 (value : Nat) (lower : 208 ≤ value) (upper : value < 224)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_14 (value : Nat) (lower : 224 ≤ value) (upper : value < 240)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

private theorem range_15 (value : Nat) (lower : 240 ≤ value) (upper : value < 256)
    (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  interval_cases value <;> intro anchors stack <;> cases globals <;> repeat first
    | exact .refl
    | refine .next rfl ?_

theorem heap_result (value : Nat) (bounded : value < 256) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    HeapCalls.ReturnsValue P59Ast.module "char_weight" [.scalar (.int value)] heap
      (.scalar (.int (ProjectEulerSolutions.XorDecryption.charWeight value))) heap globals := by
  by_cases before_0 : value < 16
  · exact range_00 value (by omega) before_0 heap globals
  by_cases before_1 : value < 32
  · exact range_01 value (by omega) before_1 heap globals
  by_cases before_2 : value < 48
  · exact range_02 value (by omega) before_2 heap globals
  by_cases before_3 : value < 64
  · exact range_03 value (by omega) before_3 heap globals
  by_cases before_4 : value < 80
  · exact range_04 value (by omega) before_4 heap globals
  by_cases before_5 : value < 96
  · exact range_05 value (by omega) before_5 heap globals
  by_cases before_6 : value < 112
  · exact range_06 value (by omega) before_6 heap globals
  by_cases before_7 : value < 128
  · exact range_07 value (by omega) before_7 heap globals
  by_cases before_8 : value < 144
  · exact range_08 value (by omega) before_8 heap globals
  by_cases before_9 : value < 160
  · exact range_09 value (by omega) before_9 heap globals
  by_cases before_10 : value < 176
  · exact range_10 value (by omega) before_10 heap globals
  by_cases before_11 : value < 192
  · exact range_11 value (by omega) before_11 heap globals
  by_cases before_12 : value < 208
  · exact range_12 value (by omega) before_12 heap globals
  by_cases before_13 : value < 224
  · exact range_13 value (by omega) before_13 heap globals
  by_cases before_14 : value < 240
  · exact range_14 value (by omega) before_14 heap globals
  exact range_15 value (by omega) bounded heap globals
end char_weight

namespace char_weight

theorem «Returns» (value : Int)
    (nonnegative : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_0)
    (bounded : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_1) :
    (HeapCalls.scalarFunction P59Ast.module "char_weight" [.int value]).Returns := by
  have lower : 0 ≤ value := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare nonnegative rfl
  have upper : value < 256 := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare bounded rfl
  have returned :
      (HeapCalls.scalarFunction P59Ast.module "char_weight" [.int (value.toNat : Int)]).Returns :=
    HeapCalls.ReturnsValue.scalar_returns (heap_result value.toNat (by omega) [] [])
  simpa only [Int.toNat_of_nonneg lower] using returned

theorem «Supported» (value : Int)
    (nonnegative : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_0)
    (bounded : Calls.Condition P59Ast.module
      (fun name => if name = "value" then some (.int value) else none) P59Ast.requires_char_weight_1) :
    (HeapCalls.scalarFunction P59Ast.module "char_weight" [.int value]).Supported :=
  («Returns» value nonnegative bounded).supported

end char_weight

end data.«project-euler-statements».data.py.project_euler_statements.p59
