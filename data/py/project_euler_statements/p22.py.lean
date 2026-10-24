import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p22.py.ast»
import FormalSW
import ProjectEulerStatements.P22

namespace data.«project-euler-statements».data.py.project_euler_statements.p22
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := P22Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev character (c : Char) : Mutable.Value := .scalar (.string (String.ofList [c]))

private def letterDefinition : List Arg × List Stmt :=
  (findFunctionIn program.body "letter_value").getD ([], [])

/-- The source's guarded ordinal conversion implements the mathematical letter value. -/
theorem letter_value.result (c : Char) (heap : Mutable.Heap) :
    ReturnsValue program "letter_value" [character c] heap
      (number (ProjectEulerStatements.P22.letterValue c)) heap := by
  let env := setLocal (setLocal (functionEnv letterDefinition.1 letterDefinition.2 [character c] [])
    "n" (number c.toNat)) "a" (number 65)
  have first : Evaluates.Compares program env (number 65) .ltE (.name "n")
      [(.ltE, .builtinCall .ord [.constant (.string "Z")])]
      heap (.scalar (.bool (decide (65 ≤ c.toNat ∧ c.toNat ≤ 90)))) heap := by
    by_cases lower : 65 ≤ c.toNat
    · apply Evaluates.Compares.next (value := number c.toNat) (compared := .scalar (.bool true))
        (middle := heap) (afterComparison := heap) (Evaluates.lookup rfl)
      · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
        omega
      · rfl
      · apply Evaluates.Compares.last (value := number 90) (middle := heap)
        · exact Evaluates.builtin (.cons Evaluates.constant .nil) rfl
        · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
          omega
    · have rejected : decide (65 ≤ c.toNat ∧ c.toNat ≤ 90) = false := by simp [lower]
      rw [rejected]
      apply Evaluates.Compares.stop (answer := .scalar (.bool false)) (value := number c.toNat)
        (middle := heap) (finalHeap := heap) (Evaluates.lookup rfl)
      · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
        omega
      · rfl
  have test := Evaluates.chain (Evaluates.lookup (show env "a" = some (number 65) from rfl)) first
  apply BlockReturns.function (args := letterDefinition.1) (body := letterDefinition.2) rfl rfl
  apply BlockReturns.assign (value := number c.toNat) (middle := heap)
  · apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
    simp only [primitive, Strings.ord_character]
    rfl
  · apply BlockReturns.assign (value := number 65) (middle := heap)
    · exact Evaluates.builtin (.cons Evaluates.constant .nil) rfl
    · apply BlockReturns.return_value
      by_cases accepted : 65 ≤ c.toNat ∧ c.toNat ≤ 90
      · apply Evaluates.conditional test (flag := true) (by simp [Mutable.truth, scalarTruth, accepted])
        apply Evaluates.binary (av := number (c.toNat - 65)) (bv := number 1) (middle := heap) (afterRight := heap)
        · apply Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
          simp [Mutable.binary, scalarBinary, number]
        · exact Evaluates.constant
        · simp [Mutable.binary, scalarBinary, number, ProjectEulerStatements.P22.letterValue,
            show 'A'.toNat = 65 from rfl, show 'Z'.toNat = 90 from rfl, accepted,
            Int.natCast_sub accepted.1]
      · apply Evaluates.conditional test (flag := false) (by simp [Mutable.truth, scalarTruth, accepted])
        simpa [ProjectEulerStatements.P22.letterValue, show 'A'.toNat = 65 from rfl,
          show 'Z'.toNat = 90 from rfl, accepted] using
          (Evaluates.constant (module := program) (env := env) (heap := heap) (value := .int 0))

theorem fold_letter_values (characters : List Char) (initial : Nat) :
    characters.foldl (fun (total : Int) c => total + ProjectEulerStatements.P22.letterValue c) initial =
      (characters.foldl (fun total c => total + ProjectEulerStatements.P22.letterValue c) initial : Nat) := by
  induction characters generalizing initial with
  | nil => rfl
  | cons c rest ih =>
      simpa only [List.foldl_cons, Int.natCast_add] using ih (initial + ProjectEulerStatements.P22.letterValue c)

/-- Summing the source helper over a Unicode string gives the statement's name value. -/
theorem name_value.result (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "name_value" [.scalar (.string text)] heap
      (number (ProjectEulerStatements.P22.nameValue text)) heap := by
  have sequence : Mutable.sequence (.scalar (.string text)) heap =
      some (.ok (text.toList.map character), heap) := by
    simp [Mutable.sequence, character]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (by intro expressions impossible; cases impossible)
    (Evaluates.lookup rfl) sequence Evaluates.constant rfl
  change BlockReturns program _ _ heap
    (number ((text.toList.foldl (fun total c => total + ProjectEulerStatements.P22.letterValue c) 0 : Nat) : Int)) heap
  rw [← fold_letter_values]
  apply sum_map_loop (source := .scalar (.string text)) (heap := heap)
    (values := text.toList) (encode := character) text.toList (by decide) sequence
  · intro env c lookup
    exact Evaluates.call (.cons (Evaluates.lookup lookup) .nil) (letter_value.result c heap)
  · rfl
  · simp [setLocal]

theorem name_score.result (position : Int) (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "name_score" [number position, .scalar (.string text)] heap
      (number (position * ProjectEulerStatements.P22.nameValue text)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (Evaluates.lookup rfl)
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (name_value.result text heap))
  rfl

/-- The exact score of the names in the order produced by the modeled Python sort. -/
def scores (names : List String) : Int :=
  indexedSum (fun i name => i * ProjectEulerStatements.P22.nameValue name) 1 0 (ScalarSort.strings names)

/-- Sorting allocates one fresh list, while scoring leaves every existing object unchanged. -/
theorem naive.result (names : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (names.map (fun name => .scalar (.string name))))) :
    ReturnsValue program "naive" [.ref address] heap (number (scores names))
      (heap ++ [.list ((ScalarSort.strings names).map (fun name => .scalar (.string name)))]) := by
  let ordered := ScalarSort.strings names
  let allocated := heap ++ [.list (ordered.map (fun name => .scalar (.string name)))]
  have sorted : primitive (.builtin .sorted) [.ref address] heap = some (.ok (.ref heap.length), allocated) := by
    have operation := primitive_sorted_list heap address (names.map Constant.string) (ordered.map Constant.string)
      (by simpa only [List.map_map] using found) (ScalarSort.sort_strings names)
    simpa only [List.map_map] using operation
  have sequence : Mutable.sequence (.ref heap.length) allocated =
      some (.ok (ordered.map (fun name => .scalar (.string name))), allocated) := by
    simp [Mutable.sequence, allocated]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_targets_enumerate (middle := allocated) (afterStart := allocated)
    (source := .ref heap.length) (startValue := number 1)
  · apply Evaluates.Arguments.cons (middle := allocated)
    · exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) sorted
    · exact .cons Evaluates.constant .nil
  · rfl
  · exact sequence
  · rfl
  · exact Evaluates.constant
  · rfl
  · apply sum_enumerate_loop (source := .ref heap.length) (heap := allocated)
      (values := ordered) (encode := fun name => .scalar (.string name))
      ordered (by decide) (by decide) (by decide) sequence
    · intro env counter name indexLookup nameLookup
      exact Evaluates.call (.cons (Evaluates.lookup indexLookup) (.cons (Evaluates.lookup nameLookup) .nil))
        (name_score.result counter name allocated)
    · rfl
    · simp [setLocal]

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "naive" [.ref address] heap).Returns := by
  obtain ⟨names, found⟩ := Mutable.Value.strings_of_hasType typed
  exact (naive.result names heap address found).returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "naive" [.ref address] heap).Supported :=
  (naive.«Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p22
