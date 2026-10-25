import data.«project-euler-statements».data.py.project_euler_statements.«p32.values.source»
import ProjectEulerSolutions.Lib.HeapCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PandigitalProductSearch
private abbrev program := P32Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
def numbers (items : List Nat) : List Mutable.Value := items.map number

inductive Part where
  | left | middle | right

def partDigits (part : Part) (items : List Nat) (first second : Nat) : List Nat :=
  match part with
  | .left => items.take first
  | .middle => (items.drop first).take (second - first)
  | .right => items.drop second

def sliceExpr : Part → Expr
  | .left => .subscript (.name "digits") (.slice none (some (.name "first")) none)
  | .middle => .subscript (.name "digits") (.slice (some (.name "first")) (some (.name "second")) none)
  | .right => .subscript (.name "digits") (.slice (some (.name "second")) none none)

def partExpr (part : Part) : Expr := .call (.name "of_digits_be") [sliceExpr part]

def partExtra (part : Part) (items : List Nat) (first second : Nat) : Mutable.Heap :=
  [.list (numbers (partDigits part items first second)),
   .list (numbers (partDigits part items first second).reverse)]

theorem part_result (part : Part) (items : List Nat) (first second address : Nat)
    (ordered : first ≤ second) (bound : second ≤ items.length) (heap : Mutable.Heap)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getDigits : env "digits" = some (.ref address))
    (getFirst : env "first" = some (number first)) (getSecond : env "second" = some (number second)) :
    Evaluates program env (partExpr part) heap (number (value (partDigits part items first second)))
      (heap ++ partExtra part items first second) := by
  have sliced : Evaluates program env (sliceExpr part) heap (.ref heap.length)
      (heap ++ [.list (numbers (partDigits part items first second))]) := by
    cases part with
    | left =>
        apply Evaluates.slice
          (.cons (Evaluates.lookup getDigits) (.cons Evaluates.constant
            (.cons (Evaluates.lookup getFirst) (.cons Evaluates.constant .nil))))
        simpa [partDigits, numbers, FormalSW.Py.Builtin.Slice.prefixLength_nonnegative,
          Nat.min_eq_left (ordered.trans bound)] using
          Mutable.getSlice_list_prefix heap address (numbers items) first found
    | middle =>
        apply Evaluates.slice
          (.cons (Evaluates.lookup getDigits) (.cons (Evaluates.lookup getFirst)
            (.cons (Evaluates.lookup getSecond) (.cons Evaluates.constant .nil))))
        simpa [partDigits, numbers] using Mutable.getSlice_list_interval heap address (numbers items)
          first second ordered (by simpa [numbers] using bound) found
    | right =>
        apply Evaluates.slice
          (.cons (Evaluates.lookup getDigits) (.cons (Evaluates.lookup getSecond)
            (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
        simpa [partDigits, numbers] using
          Mutable.getSlice_list_suffix heap address (numbers items) second found
  have converted := of_digits_be.result (partDigits part items first second)
    (heap ++ [.list (numbers (partDigits part items first second))]) heap.length
    (by change (heap ++ [.list (numbers (partDigits part items first second))])[heap.length]? =
          some (.list (numbers (partDigits part items first second)))
        simp)
  simpa only [partExpr, partExtra, List.append_assoc, List.singleton_append] using
    Evaluates.call (module := program) (env := env) (.cons sliced .nil) converted

end data.«project-euler-statements».data.py.project_euler_statements.p32.naive
