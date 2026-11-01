import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».EncodeTable

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false

abbrev rawTokens : List (Nat × List String) := tokens.map (fun pair => (pair.1, pair.2.toList.map String.singleton))
def entryExpression (pair : Nat × List String) : Expr :=
  .tuple [.constant (.int pair.1), .list (pair.2.map (fun text => .constant (.string text)))]
def rawModel (pair : Nat × List String) : Nat × List Mutable.Value := (pair.1, pair.2.map string)

theorem Entry.Valid.append {base : Mutable.Heap} {entry : Entry} (valid : entry.Valid base) (extra : Mutable.Heap) :
    entry.Valid (base ++ extra) :=
  ⟨valid.positive, HeapCollection.prefix_found base extra _ _ valid.pair,
    HeapCollection.prefix_found base extra _ _ valid.token⟩

theorem string_arguments (texts : List String) (heap : Mutable.Heap) (env : HeapCalls.Env) :
    Evaluates.Arguments program env (texts.map (fun text => .constant (.string text))) heap (texts.map string) heap := by
  induction texts with
  | nil => exact .nil
  | cons text rest ih => exact .cons Evaluates.constant ih

/-- Each literal token list is allocated before its pair tuple, in source evaluation order. -/
theorem allocate_entries (raw : List (Nat × List String)) (positive : ∀ pair ∈ raw, 0 < pair.1)
    (heap : Mutable.Heap) (env : HeapCalls.Env) :
    ∃ (extra : Mutable.Heap) (entries : List Entry),
      Evaluates.Arguments program env (raw.map entryExpression) heap (entries.map Entry.reference) (heap ++ extra) ∧
      (∀ entry ∈ entries, entry.Valid (heap ++ extra)) ∧
      entries.map Entry.model = raw.map rawModel := by
  induction raw generalizing heap with
  | nil => exact ⟨[], [], by simpa using (Evaluates.Arguments.nil (module := program) (env := env) (heap := heap)),
      by simp, rfl⟩
  | cons pair rest ih =>
      let first : Entry := ⟨pair.1, pair.2.map string, heap.length + 1, heap.length⟩
      let objects : Mutable.Heap := [.list (pair.2.map string), .tuple [number pair.1, .ref heap.length]]
      let pairHeap := heap ++ objects
      have evaluated : Evaluates program env (entryExpression pair) heap first.reference pairHeap := by
        have fields : Evaluates.Arguments program env
            [.constant (.int pair.1), .list (pair.2.map (fun text => .constant (.string text)))] heap
            [number pair.1, .ref heap.length] (heap ++ [.list (pair.2.map string)]) :=
          .cons Evaluates.constant (.cons (Evaluates.list (string_arguments pair.2 heap env)) .nil)
        simpa [entryExpression, first, Entry.reference, pairHeap, objects, List.append_assoc] using
          Evaluates.tuple fields (by simp)
      have firstValid : first.Valid pairHeap := by
        constructor
        · exact positive pair (by simp)
        · simp [first, pairHeap, objects]
        · simp [first, pairHeap, objects]
      obtain ⟨extra, entries, arguments, valid, models⟩ := ih (fun p member => positive p (by simp [member])) pairHeap
      refine ⟨objects ++ extra, first :: entries, ?_, ?_, ?_⟩
      · simpa only [List.map_cons, pairHeap, List.append_assoc] using Evaluates.Arguments.cons evaluated arguments
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [pairHeap, List.append_assoc] using firstValid.append extra
        · simpa only [pairHeap, List.append_assoc] using valid entry member
      · simp only [List.map_cons, models]
        rfl

/-- The complete literal table has positive denominations and the exact canonical token contents. -/
theorem allocate_table (heap : Mutable.Heap) (env : HeapCalls.Env) :
    ∃ (extra : Mutable.Heap) (entries : List Entry),
      Evaluates program env (.list (rawTokens.map entryExpression)) heap (.ref (heap ++ extra).length)
        ((heap ++ extra) ++ [.list (entries.map Entry.reference)]) ∧
      (∀ entry ∈ entries, entry.Valid ((heap ++ extra) ++ [.list (entries.map Entry.reference)])) ∧
      entries.map Entry.model = rawTokens.map rawModel := by
  have positive : ∀ pair ∈ rawTokens, 0 < pair.1 := by decide
  obtain ⟨extra, entries, arguments, valid, models⟩ := allocate_entries rawTokens positive heap env
  exact ⟨extra, entries, Evaluates.list arguments, fun entry member => (valid entry member).append _, models⟩

end data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
