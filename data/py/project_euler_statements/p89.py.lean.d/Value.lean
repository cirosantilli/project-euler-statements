import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p89.py.ast»
import lang.py.FormalSW.DictionaryCalls
import ProjectEulerSolutions.Lib.RomanNumerals

namespace data.«project-euler-statements».data.py.project_euler_statements.p89
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
set_option Elab.async false

abbrev program := P89Ast.module
abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
abbrev string (text : String) : Mutable.Value := .scalar (.string text)

def valueTable : List (Constant × Constant) :=
  [(.string "I", .int 1), (.string "V", .int 5), (.string "X", .int 10), (.string "L", .int 50),
    (.string "C", .int 100), (.string "D", .int 500), (.string "M", .int 1000)]

def valueEntries : List (Constant × Mutable.Value) :=
  valueTable.foldl (fun entries (key, value) => ScalarDict.insert entries key (.scalar value)) []

theorem value_lookup (text : String) (valid : text ∈ RomanNumerals.symbols) :
    ScalarDict.lookup valueEntries (.string text) = some (number (RomanNumerals.value text)) := by
  simp only [RomanNumerals.symbols, List.mem_cons, List.not_mem_nil, or_false] at valid
  rcases valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem value_default (text : String) :
    (ScalarDict.lookup valueEntries (.string text)).getD (number 0) = number (RomanNumerals.value text) := by
  by_cases valid : text ∈ RomanNumerals.symbols
  · rw [value_lookup text valid]
    rfl
  · have outside : text ≠ "I" ∧ text ≠ "V" ∧ text ≠ "X" ∧ text ≠ "L" ∧
        text ≠ "C" ∧ text ≠ "D" ∧ text ≠ "M" := by simpa [RomanNumerals.symbols] using valid
    rcases outside with ⟨hi, hv, hx, hl, hc, hd, hm⟩
    change (ScalarDict.lookup
      [(.string "I", number 1), (.string "V", number 5), (.string "X", number 10), (.string "L", number 50),
        (.string "C", number 100), (.string "D", number 500), (.string "M", number 1000)]
      (.string text)).getD (number 0) = _
    simp [ScalarDict.lookup, scalarCompare, RomanNumerals.value,
      hi, hv, hx, hl, hc, hd, hm, Ne.symm hi, Ne.symm hv, Ne.symm hx, Ne.symm hl, Ne.symm hc, Ne.symm hd, Ne.symm hm]

/-- The reference's local dictionary uses Python string equality and defaults to zero. -/
theorem value.result (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "value" [string text] heap (number (RomanNumerals.value text)) (heap ++ [.dict valueEntries]) := by
  have found : (heap ++ [.dict valueEntries])[heap.length]? = some (.dict valueEntries) := by simp
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.dictionary_get (entries := valueEntries)
    (by intro name same; cases same) (Evaluates.dictionary_constants valueTable)
  · exact found
  · exact .cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil)
  · change Mutable.dictionaryGet heap.length (string text) (number 0) (heap ++ [.dict valueEntries]) = _
    rw [Mutable.dictionaryGet_scalar _ _ valueEntries found, value_default]

end data.«project-euler-statements».data.py.project_euler_statements.p89
