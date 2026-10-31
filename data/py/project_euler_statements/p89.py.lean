import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Parse
import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».EncodeLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p89
open FormalSW.PyAst
set_option Elab.async false

theorem value.«Returns» (text : String) :
    (HeapCalls.scalarFunction program "value" [.string text]).Returns :=
  (value.result text []).scalar_returns

theorem value.«Supported» (text : String) :
    (HeapCalls.scalarFunction program "value" [.string text]).Supported :=
  (value.«Returns» text).supported

theorem roman_to_int.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "roman_to_int" [.ref address] heap).Returns := by
  obtain ⟨input, found⟩ := Mutable.Value.strings_of_hasType typed
  obtain ⟨_, returned⟩ := roman_to_int.result input heap address found
  exact returned.returns

theorem roman_to_int.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "roman_to_int" [.ref address] heap).Supported :=
  (roman_to_int.«Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p89
