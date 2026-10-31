import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Value
import ProjectEulerSolutions.Lib.HeapCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.roman_to_int
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
set_option Elab.async false

abbrev code : List Stmt := executableBody ((findFunctionIn program.body "roman_to_int").getD ([], [])).2
abbrev encode (input : List String) : List Mutable.Value := input.map string

theorem empty_test (input : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode input))) (env : HeapCalls.Env)
    (getInput : env "chars" = some (.ref address)) :
    Evaluates program env (.unaryOp .not (.name "chars")) heap
      (.scalar (.bool input.isEmpty)) heap := by
  apply Evaluates.unary (Evaluates.lookup getInput)
  cases input <;> simp [HeapCalls.unary, Mutable.truth, found, encode]

theorem length_test (input : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode input))) (env : HeapCalls.Env)
    (getInput : env "chars" = some (.ref address)) :
    Evaluates program env (.compare (.builtinCall .len [.name "chars"]) [(.eq, .constant (.int 1))])
      heap (.scalar (.bool (decide (input.length = 1)))) heap := by
  apply Evaluates.compare (av := number input.length) (bv := number 1) (middle := heap) (afterRight := heap)
  · apply Evaluates.builtin (.cons (Evaluates.lookup getInput) .nil)
    simp [primitive, Mutable.length, found, encode, number]
  · exact Evaluates.constant
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem read (input : List String) (index : Nat) (inside : index < input.length)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (encode input)))
    (env : HeapCalls.Env) (getInput : env "chars" = some (.ref address)) :
    Evaluates program env (.subscript (.name "chars") (.constant (.int index))) heap (string input[index]) heap := by
  apply Evaluates.subscript (by intros; simp) (Evaluates.lookup getInput) Evaluates.constant
  have actual : (encode input)[index]'(by simpa using inside) = string input[index] := by
    exact List.getElem_map string
  have fetched := Mutable.getItem_list heap address index (encode input) found (by simpa using inside)
  rw [actual] at fetched
  exact fetched

theorem slice (input : List String) (count : Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode input))) (env : HeapCalls.Env)
    (getInput : env "chars" = some (.ref address)) :
    Evaluates program env (.subscript (.name "chars") (.slice (some (.constant (.int count))) none none))
      heap (.ref heap.length) (heap ++ [.list (encode (input.drop count))]) := by
  apply Evaluates.slice (receiver := .ref address) (first := number count)
    (last := .scalar .none) (stepValue := .scalar .none) (middle := heap)
  · exact .cons (Evaluates.lookup getInput) (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil)))
  · simpa only [encode, List.map_drop] using Mutable.getSlice_list_suffix heap address (encode input) count found

theorem value_call (text : String) (expression : Expr) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (evaluated : Evaluates program env expression heap (string text) heap) :
    Evaluates program env (.call (.name "value") [expression]) heap (number (RomanNumerals.value text))
      (heap ++ [.dict valueEntries]) :=
  Evaluates.call (.cons evaluated .nil) (value.result text heap)

def pairEnv (env : HeapCalls.Env) (first second : String) : HeapCalls.Env :=
  assignNames env ["a", "b"] [string first, string second]

theorem unpack_pair (first second : String) (rest : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode (first :: second :: rest))))
    (env : HeapCalls.Env) (getInput : env "chars" = some (.ref address)) :
    BlockContinues program env [code[2]'(by decide)] heap (pairEnv env first second)
      (heap ++ [.tuple [string first, string second]]) := by
  have evaluated : Evaluates program env
      (.tuple [.subscript (.name "chars") (.constant (.int 0)), .subscript (.name "chars") (.constant (.int 1))])
      heap (.ref heap.length) (heap ++ [.tuple [string first, string second]]) := by
    apply Evaluates.tuple
    · exact .cons (read _ 0 (by simp) heap address found env getInput)
        (.cons (read _ 1 (by simp) heap address found env getInput) .nil)
    · simp
  have sequence : Mutable.sequence (.ref heap.length) (heap ++ [.tuple [string first, string second]]) =
      some (.ok [string first, string second], heap ++ [.tuple [string first, string second]]) := by
    simp [Mutable.sequence]
  exact BlockContinues.unpack rfl evaluated sequence rfl

theorem comparison (first second : String) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getFirst : env "a" = some (string first)) (getSecond : env "b" = some (string second)) :
    Evaluates program env
      (.compare (.call (.name "value") [.name "a"]) [(.lt, .call (.name "value") [.name "b"])])
      heap (.scalar (.bool (decide (RomanNumerals.value first < RomanNumerals.value second))))
      (heap ++ [.dict valueEntries, .dict valueEntries]) := by
  apply Evaluates.compare (value_call first (.name "a") heap env (Evaluates.lookup getFirst))
    (value_call second (.name "b") (heap ++ [.dict valueEntries]) env (Evaluates.lookup getSecond))
  simp [HeapCalls.compare, scalarCompare, evalCmpOp, List.append_assoc]

end data.«project-euler-statements».data.py.project_euler_statements.p89.roman_to_int
