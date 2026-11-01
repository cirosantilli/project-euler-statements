import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Parse
import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Encode

namespace data.«project-euler-statements».data.py.project_euler_statements.p89
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false
variable {globals : Mutable.Globals}

def characters (text : String) : List String := text.toList.map String.singleton
def decoded (text : String) : Nat := parse (characters text)
def minimal (text : String) : String := String.ofList (canonical (decoded text))
def saved (text : String) : Int := (text.length : Int) - (canonical (decoded text)).length

/-- list(s), recursive parsing, token encoding, and join all follow the actual reference expression. -/
theorem minimal_roman.result (text : String) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "minimal_roman" [string text] heap (string (minimal text)) (heap ++ extra) := by
  have argument : functionEnv ((findFunctionIn program.body "minimal_roman").getD ([], [])).1
      ((findFunctionIn program.body "minimal_roman").getD ([], [])).2 [string text] globals "s" = some (string text) := by
    cases globals <;> rfl
  let input := roman_to_int.encode (characters text)
  let listedHeap := heap ++ [.list input]
  obtain ⟨parsedExtra, parsed⟩ := roman_to_int.result (globals := globals) (characters text) listedHeap heap.length (by simp [listedHeap, input])
  let parsedHeap := listedHeap ++ parsedExtra
  obtain ⟨encodedExtra, encoded⟩ := int_to_roman_aux.result (globals := globals) (decoded text) parsedHeap
  let resultBase := parsedHeap ++ encodedExtra
  let finalHeap := resultBase ++ [.list (int_to_roman_aux.outputValues (decoded text))]
  have returned : ReturnsValue (globals := globals) program "minimal_roman" [string text] heap (string (minimal text)) finalHeap := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.join (values := [.ref resultBase.length]) (afterArguments := finalHeap) Evaluates.constant
    · apply Evaluates.Arguments.cons
      · apply Evaluates.call (values := [number (decoded text)]) (middle := parsedHeap)
        · apply Evaluates.Arguments.cons
          · apply Evaluates.call (values := [.ref heap.length]) (middle := listedHeap)
            · apply Evaluates.Arguments.cons
              · apply Evaluates.builtin (values := [string text]) (middle := heap) (finalHeap := listedHeap)
                  (.cons (Evaluates.lookup argument) .nil)
                simp [primitive, Mutable.sequence, Mutable.allocate, listedHeap, input,
                  roman_to_int.encode, characters, string, List.map_map, Except.map]
              · exact .nil
            · exact parsed
          · exact .nil
        · exact encoded
      · exact .nil
    · have found : finalHeap[resultBase.length]? =
          some (.list (((canonical (decoded text)).map String.singleton).map (fun s => Mutable.Value.scalar (.string s)))) := by
        simp [finalHeap, int_to_roman_aux.outputValues, string, List.map_map]
      simpa only [join_characters] using primitive_join_list finalHeap resultBase.length ""
        ((canonical (decoded text)).map String.singleton) found
    · intros name impossible
      cases impossible
  refine ⟨[.list input] ++ parsedExtra ++ encodedExtra ++ [.list (int_to_roman_aux.outputValues (decoded text))], ?_⟩
  simpa only [finalHeap, resultBase, parsedHeap, listedHeap, List.append_assoc] using returned

/-- The reference subtracts lengths as signed integers, including noncanonical symbol strings. -/
theorem saved_chars.result (text : String) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "saved_chars" [string text] heap (.scalar (.int (saved text))) (heap ++ extra) := by
  have argument : functionEnv ((findFunctionIn program.body "saved_chars").getD ([], [])).1
      ((findFunctionIn program.body "saved_chars").getD ([], [])).2 [string text] globals "s" = some (string text) := by
    cases globals <;> rfl
  obtain ⟨extra, rendered⟩ := minimal_roman.result (globals := globals) text heap
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number text.length) (bv := number (minimal text).length)
    (middle := heap) (afterRight := heap ++ extra)
  · apply Evaluates.builtin (.cons (Evaluates.lookup argument) .nil)
    rfl
  · apply Evaluates.builtin (values := [string (minimal text)]) (middle := heap ++ extra)
    · exact .cons (Evaluates.call (.cons (Evaluates.lookup argument) .nil) rendered) .nil
    · rfl
  · simp [Mutable.binary, scalarBinary, saved, minimal]

end data.«project-euler-statements».data.py.project_euler_statements.p89
