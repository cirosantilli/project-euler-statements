import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p42.py.ast»
import lang.py.FormalSW.TruthCalls
import ProjectEulerSolutions.Lib.FilteredSum
import ProjectEulerSolutions.Lib.TriangularDiscriminant

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p42
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.TriangularDiscriminant
private abbrev program := P42Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private abbrev character (c : Char) : Mutable.Value := .scalar (.string (String.singleton c))
private abbrev string (s : String) : Mutable.Value := .scalar (.string s)

def letter (c : Char) : Int := (c.toNat : Int) - 65 + 1
def score (text : String) : Int := text.toList.foldl (fun total c => total + letter c) 0
def triangularTest (n : Int) : Bool :=
  if n < 0 then false else ProjectEulerStatements.P42.isTriangle n.toNat
def count (words : List String) : Int :=
  words.foldl (fun total w => if triangularTest (score w) then total + 1 else total) 0

namespace word_value
/-- The reference sums raw Unicode ordinals, even outside the solver's uppercase domain. -/
theorem result (text : String) (heap : Mutable.Heap) :
    ReturnsValue program "word_value" [string text] heap (number (score text)) heap := by
  have sequence : Mutable.sequence (string text) heap = some (.ok (text.toList.map character), heap) := by
    simp [Mutable.sequence]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (by intros; simp)
    (Evaluates.lookup rfl) sequence Evaluates.constant rfl
  apply sum_map_loop (source := .scalar (.string text)) (values := text.toList)
    (encode := character) (number := letter) text.toList (by decide) sequence
  · intro env c found
    apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (av := number ((c.toNat : Int)-65)) (bv := number 1)
    · apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
        (av := number c.toNat) (bv := number 65)
      · apply Evaluates.builtin (.cons (Evaluates.lookup found) .nil)
        change scalarResult (some (Strings.ord (.string (String.singleton c)))) heap = _
        rw [String.singleton_eq_ofList, Strings.ord_character]
        rfl
      · exact Evaluates.builtin (.cons Evaluates.constant .nil) rfl
      · rfl
    · exact Evaluates.constant
    · rfl
  · rfl
  · simp [setLocal]
end word_value

namespace is_triangle
private abbrev candidate : Expr :=
  .binOp (.binOp (.name "k") .mult (.binOp (.name "k") .add (.constant (.int 1))))
    .floorDiv (.constant (.int 2))
private abbrev condition : Expr := .compare candidate [(.eq, .name "n")]

private theorem candidate_result (k : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getK : env "k" = some (number k)) :
    Evaluates program env candidate heap (number (triangular k)) heap := by
  apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
    (av := number (k*(k+1))) (bv := number 2)
  · apply Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (av := number k) (bv := number (k+1)) (Evaluates.lookup getK)
    · exact Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
        (Evaluates.lookup getK) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
    · simp [Mutable.binary, scalarBinary, number]
  · exact Evaluates.constant
  · simp [Mutable.binary, scalarBinary, number, triangular]

private theorem loop (n first remaining stop : Nat) (length : first+remaining=stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getN : env "n" = some (number n)) :
    BlockReturns program env
      [.rangeStepLoop "k" first stop 1 (truthBody false condition) [], .return (.constant (.bool false))]
      heap (flag ((List.range' first remaining).any (fun k => decide (triangular k=n)))) heap := by
  induction remaining generalizing first env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ remaining ih =>
      let bound := setLocal env "k" (number first)
      have tested : Evaluates program bound condition heap (flag (decide (triangular first=n))) heap := by
        apply Evaluates.compare (middle := heap) (afterRight := heap)
          (candidate_result first heap bound rfl) (Evaluates.lookup (by simpa [bound, setLocal] using getN))
        change some (Except.ok (ε := ExceptionObject) (flag (decide ((triangular first : Int)=(n : Int)))), heap) = _
        simp only [Int.natCast_inj]
      rw [List.range'_succ, List.any_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      by_cases found : triangular first = n
      · simp only [found, decide_true, Bool.true_or]
        apply BlockReturns.branch (flag := true) tested
        · simp [Mutable.truth, scalarTruth, found]
        · exact BlockReturns.return_value Evaluates.constant
      · simp only [found, decide_false, Bool.false_or]
        apply BlockReturns.branch (flag := false) tested
        · simp [Mutable.truth, scalarTruth, found]
        · have rest := ih (first+1) (by omega) bound (by simpa [bound, setLocal] using getN)
          simpa only [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append,
            Int.natCast_add, Int.natCast_one] using rest

/-- The reference's finite range also terminates for negative integers. -/
theorem result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "is_triangle" [number n] heap (flag (triangularTest n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.truth_generator_range (universal := false)
    (values := [number (n+1)])
    (.cons (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup rfl) Evaluates.constant rfl) .nil) rfl
  by_cases negative : n < 0
  · apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    simpa only [triangularTest, if_pos negative] using
      (BlockReturns.return_value (module := program) (heap := heap) (env := _)
        (Evaluates.constant (value := .bool false)))
  · lift n to Nat using (by omega : 0 ≤ n)
    let initial := functionEnv ((findFunctionIn program.body "is_triangle").getD ([], [])).1
      ((findFunctionIn program.body "is_triangle").getD ([], [])).2 [number n] []
    let inner := comprehensionTargetsEnv initial
      [(.name "k", .call (.name "range") [.binOp (.name "n") .add (.constant (.int 1))], [])]
    have executed := loop n 0 (n+1) (n+1) (by omega) heap inner (by simp [inner, initial, comprehensionTargetsEnv, targetLocals]; rfl)
    simpa only [triangularTest, if_neg (by omega : ¬ (n : Int) < 0), Int.toNat_natCast,
      ProjectEulerStatements.P42.isTriangle, List.range_eq_range', triangular,
      Int.natCast_add, Int.natCast_one] using executed
end is_triangle

namespace naive
private abbrev predicate : Expr := .call (.name "is_triangle") [.call (.name "word_value") [.name "w"]]

theorem result (words : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (words.map string))) :
    ReturnsValue program "naive" [.ref address] heap (number (count words)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (items := words.map string) (by intros; simp) (Evaluates.lookup rfl)
    (by simp [Mutable.sequence, found]) Evaluates.constant rfl
  apply ProjectEulerSolutions.FilteredSum.loop (values := words) (encode := string)
    (predicate := fun w => triangularTest (score w)) (number := fun _ => 1) words (by decide)
  · simp [sequenceValue, sequenceSource, Mutable.sequence, found]
  · intro env word getW
    exact Evaluates.call
      (.cons (Evaluates.call (.cons (Evaluates.lookup getW) .nil) (word_value.result word heap)) .nil)
      (is_triangle.result (score word) heap)
  · intros
    exact Evaluates.constant
  · rfl
  · simp [setLocal]

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "naive" [.ref address] heap).Returns := by
  obtain ⟨words, found⟩ := Mutable.Value.strings_of_hasType typed
  exact (result words heap address found).returns

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[str]") :
    (HeapCalls.call program "naive" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported
end naive

end data.«project-euler-statements».data.py.project_euler_statements.p42
