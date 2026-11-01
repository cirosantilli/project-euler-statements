import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Execution

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

theorem int_to_roman_aux.«Returns» (n : Int) :
    (HeapCalls.call program "int_to_roman_aux" [.scalar (.int n)] []).Returns := by
  obtain ⟨_, returned⟩ := int_to_roman_aux.result n []
  exact returned.returns

theorem int_to_roman_aux.«Supported» (n : Int) :
    (HeapCalls.call program "int_to_roman_aux" [.scalar (.int n)] []).Supported :=
  (int_to_roman_aux.«Returns» n).supported

theorem minimal_roman.«Returns» (text : String) :
    (HeapCalls.scalarFunction program "minimal_roman" [.string text]).Returns := by
  obtain ⟨_, returned⟩ := minimal_roman.result text []
  exact returned.scalar_returns

theorem minimal_roman.«Supported» (text : String) :
    (HeapCalls.scalarFunction program "minimal_roman" [.string text]).Supported :=
  (minimal_roman.«Returns» text).supported

theorem saved_chars.«Returns» (text : String) :
    (HeapCalls.scalarFunction program "saved_chars" [.string text]).Returns := by
  obtain ⟨_, returned⟩ := saved_chars.result text []
  exact returned.scalar_returns

theorem saved_chars.«Supported» (text : String) :
    (HeapCalls.scalarFunction program "saved_chars" [.string text]).Supported :=
  (saved_chars.«Returns» text).supported

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "naive" [.ref address] heap).Returns := by
  obtain ⟨input, found⟩ := Mutable.Value.strings_of_hasType typed
  obtain ⟨_, returned⟩ := naive.result input heap address found
  exact returned.returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "naive" [.ref address] heap).Supported :=
  (naive.«Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p89
