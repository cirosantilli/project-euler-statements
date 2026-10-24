import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p49.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.PrimePermutations
import ProjectEulerSolutions.Lib.PrimePermutationReference
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.HeapTruthCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p49
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PrimePermutations
private abbrev program := P49Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def numbers (values : List Int) : List Mutable.Value := values.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 6++CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digits_sorted", "is_permutation", "seq_from", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private def digitObjects (n : Nat) : Mutable.Heap :=
  [.list (numbers (integerDigits n)), .list (numbers (sortedDigits n))]

namespace digits_sorted
/-- The source allocates its little-endian digits and a fresh sorted result, preserving every prior object. -/
theorem result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digits_sorted" [number n] heap (.ref (heap.length+1)) (heap++digitObjects n) := by
  let middle := heap++[Mutable.Object.list (numbers (integerDigits n))]
  have converted : ReturnsValue program "digits_le" [number n] heap (.ref heap.length) middle := by
    simpa only [middle, numbers, integerDigits, List.map_map, Function.comp_def] using
      (common.digits_le.decimal n heap).extend common_extension
  have sorted := primitive_sorted_list middle heap.length ((integerDigits n).map Constant.int)
    ((sortedDigits n).map Constant.int)
    (by simp [middle, numbers, number, List.map_map]) (ScalarSort.sort_ints (integerDigits n))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) converted) .nil)
  simpa [middle, digitObjects, numbers, number, List.map_map, List.append_assoc] using sorted

theorem «Returns» (n : Int)
    (condition : Calls.Condition program (fun name => if name="n" then some (.int n) else none) P49Ast.requires_digits_sorted_0) :
    (HeapCalls.call program "digits_sorted" [number n] []).Returns := by
  have nonnegative : 0≤n := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  exact (result n []).returns

theorem «Supported» (n : Int)
    (condition : Calls.Condition program (fun name => if name="n" then some (.int n) else none) P49Ast.requires_digits_sorted_0) :
    (HeapCalls.call program "digits_sorted" [number n] []).Supported := («Returns» n condition).supported
end digits_sorted

namespace is_permutation
/-- Both sorted lists are compared by contents after all argument allocations have occurred. -/
theorem result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_permutation" [number a, number b] heap
      (flag (ProjectEulerStatements.P49.isPermutation a b)) (heap++digitObjects a++digitObjects b) := by
  rw [← permutation_statement]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (av := .ref (heap.length+1)) (bv := .ref ((heap++digitObjects a).length+1))
    (middle := heap++digitObjects a) (afterRight := heap++digitObjects a++digitObjects b)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_sorted.result a heap)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_sorted.result b (heap++digitObjects a))
  · apply compare_int_lists (sortedDigits a) (sortedDigits b)
    · simp [digitObjects, numbers, List.append_assoc]
    · simp [digitObjects, numbers, List.append_assoc, Nat.add_assoc]

private abbrev inputEnv (a b : Int) : ScalarEnv :=
  fun name => if name="a" then some (.int a) else if name="b" then some (.int b) else none

private theorem condition_result (a b : Int) :
    Calls.Evaluates program (inputEnv a b) P49Ast.requires_is_permutation_0 (.bool (decide (0≤a ∧ 0≤b))) := by
  have left : Calls.Evaluates program (inputEnv a b) (.compare (.name "a") [(.gtE, .constant (.int 0))])
      (.bool (decide (0≤a))) := Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant rfl
  have right : Calls.Evaluates program (inputEnv a b) (.compare (.name "b") [(.gtE, .constant (.int 0))])
      (.bool (decide (0≤b))) := Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant rfl
  by_cases lower : 0≤a
  · apply Calls.Evaluates.boolean_continue (by simpa only [lower, decide_true] using left) rfl
    apply Calls.Evaluates.boolean_last
    simpa only [lower, true_and] using right
  · simp only [lower, false_and, decide_false]
    exact Calls.Evaluates.boolean_stop (by simpa only [lower, decide_false] using left) rfl

theorem «Returns» (a b : Int) (condition : Calls.Condition program (inputEnv a b) P49Ast.requires_is_permutation_0) :
    (HeapCalls.scalarFunction program "is_permutation" [.int a, .int b]).Returns := by
  have bounds : 0≤a ∧ 0≤b := by simpa using (condition_result a b).condition_iff.mp condition
  lift a to Nat using bounds.1
  lift b to Nat using bounds.2
  exact (result a b []).scalar_returns

theorem «Supported» (a b : Int) (condition : Calls.Condition program (inputEnv a b) P49Ast.requires_is_permutation_0) :
    (HeapCalls.scalarFunction program "is_permutation" [.int a, .int b]).Supported := («Returns» a b condition).supported
end is_permutation

namespace seq_from
private def expression : Expr := .binOp (.name "a") .add (.binOp (.name "i") .mult (.name "d"))

private theorem loop (a d : Int) (first count stop : Nat) (length : first+count=stop)
    (base : Mutable.Heap) (values : List Int) (env : HeapCalls.Env)
    (getA : env "a"=some (number a)) (getD : env "d"=some (number d)) :
    ∃ finalEnv, BlockContinues program env
      [.rangeStepLoop "i" first stop 1 [.comprehensionAppend base.length expression] []]
      (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) finalEnv
      (ProjectEulerSolutions.HeapCollection.working base
        (numbers (values++(List.range' first count).map (fun (i : Nat) => a+(i : Int)*d))) []) := by
  induction count generalizing first values env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.map_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "i" (number first)
      have boundA : bound "a"=some (number a) := by simpa [bound, setLocal] using getA
      have boundD : bound "d"=some (number d) := by simpa [bound, setLocal] using getD
      have evaluated : Evaluates program bound expression
          (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) (number (a+(first : Int)*d))
          (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) := by
        exact Evaluates.binary (av := number a) (bv := number ((first : Int)*d))
          (Evaluates.lookup boundA)
          (Evaluates.binary (av := number first) (bv := number d) (Evaluates.lookup rfl) (Evaluates.lookup boundD) rfl) rfl
      have emitted := ProjectEulerSolutions.HeapCollection.emit base (numbers values) [] [] (number (a+(first : Int)*d))
        (by simpa only [List.append_nil] using evaluated)
      obtain ⟨finalEnv, rest⟩ := ih (first+1) (by omega) (values++[a+(first : Int)*d]) bound boundA boundD
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      have firstStep : BlockContinues program bound [.comprehensionAppend base.length expression]
          (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) bound
          (ProjectEulerSolutions.HeapCollection.working base (numbers (values++[a+(first : Int)*d])) []) := by
        simpa only [numbers, List.map_append, List.map_cons, List.map_nil, List.append_nil] using emitted
      simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.map_cons,
        List.append_assoc, List.singleton_append, Int.natCast_add, Int.natCast_one] using firstStep.append rest

/-- The source comprehension terminates for every signed start, difference and length. -/
theorem result (a d length : Int) (heap : Mutable.Heap) :
    ReturnsValue program "seq_from" [number a, number d, number length] heap (.ref heap.length)
      (heap++[.list (numbers (progression a d length.toNat))]) := by
  let initial := functionEnv ((findFunctionIn program.body "seq_from").getD ([], [])).1
    ((findFunctionIn program.body "seq_from").getD ([], [])).2 [number a, number d, number length] []
  let inner := comprehensionEnv initial [("i", .call (.name "range") [.name "length"], [])]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases below : length<0
  · have empty : length.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    simp only [empty, progression, List.range_zero, List.map_nil, numbers]
    apply Evaluates.list_comp_range (.cons (Evaluates.lookup rfl) .nil) rfl
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  · lift length to Nat using (by omega : 0≤length)
    obtain ⟨finalEnv, run⟩ := loop a d 0 length length (by omega) heap [] inner rfl rfl
    apply Evaluates.list_comp_range (finalEnv := finalEnv) (.cons (Evaluates.lookup rfl) .nil) rfl
    simpa only [ProjectEulerSolutions.HeapCollection.working, numbers, List.map_nil, List.nil_append,
      progression, Int.toNat_natCast, List.range_eq_range'] using run

theorem «Returns» (a d length : Int) : (HeapCalls.call program "seq_from" [number a, number d, number length] []).Returns :=
  (result a d length []).returns

theorem «Supported» (a d length : Int) : (HeapCalls.call program "seq_from" [number a, number d, number length] []).Supported :=
  («Returns» a d length).supported
end seq_from

namespace naive
private def naturals (items : List Nat) : List Mutable.Value := items.map (fun (n : Nat) => number n)
private abbrev primeElement : Expr := .call (.name "is_prime") [.name "x"]
private abbrev primeAll : Expr := .consumeGenerator (.builtinCall .all []) primeElement [(.name "x", .name "s", [])]
private abbrev permutationElement : Expr := .call (.name "is_permutation")
  [.subscript (.name "s") (.constant (.int 0)), .name "y"]
private abbrev tailExpression : Expr := .subscript (.name "s") (.slice (some (.constant (.int 1))) none none)
private abbrev permutationAll : Expr := .consumeGenerator (.builtinCall .all []) permutationElement
  [(.name "y", tailExpression, [])]

private theorem prime_all (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]?=some (.list (naturals items))) (env : HeapCalls.Env)
    (getS : env "s"=some (.ref address)) :
    Evaluates program env primeAll heap
      (flag (ProjectEulerStatements.P49.allPrime items)) heap := by
  apply Evaluates.all_map (α := Nat) (values := items) (encode := fun n => number n)
    (predicate := fun n => decide (Nat.Prime n))
    (by intros; simp) (by intros; simp) (by intros; simp) (Evaluates.lookup getS)
    (by simp [Mutable.sequence, found, naturals])
  intro inner item getX
  exact Evaluates.call (.cons (Evaluates.lookup getX) .nil)
    ((common.is_prime.heap_result item heap).extend common_extension)

/-- Every permutation predicate sees the original sequence after earlier predicate allocations. -/
private theorem permutation_all (head : Nat) (tail : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]?=some (.list (naturals (head::tail)))) (env : HeapCalls.Env)
    (getS : env "s"=some (.ref address)) :
    ∃ extra, Evaluates program env permutationAll heap
      (flag (ProjectEulerStatements.P49.allPerm (head::tail))) (heap++extra) := by
  let middle := heap++[Mutable.Object.list (naturals tail)]
  have sliced : Evaluates program env tailExpression heap (.ref heap.length) middle := by
    apply Evaluates.slice (.cons (Evaluates.lookup getS)
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa [middle, naturals, List.map_drop] using
      Mutable.getSlice_list_suffix heap address (naturals (head::tail)) 1 found
  let invariant := fun inner : HeapCalls.Env => inner "s"=some (.ref address)
  obtain ⟨extra, checked⟩ := ProjectEulerSolutions.HeapTruthCollection.all_map (α := Nat) program tail
    (fun n => number n) (ProjectEulerStatements.P49.isPermutation head) "y" permutationElement tailExpression
    heap middle heap.length env (by intros; simp) (by intros; simp) (by intros; simp) sliced
    (by simp [middle, naturals]) invariant
    (by intro inner item valid; simpa [invariant, setLocal] using valid)
    (by
      intro garbage inner item valid getY
      have sourceFound : (middle++garbage)[address]?=some (.list (naturals (head::tail))) :=
        ProjectEulerSolutions.HeapCollection.prefix_found middle garbage address _
          (ProjectEulerSolutions.HeapCollection.prefix_found heap _ address _ found)
      have first : Evaluates program inner (.subscript (.name "s") (.constant (.int 0)))
          (middle++garbage) (number head) (middle++garbage) := by
        apply Evaluates.subscript (by intros; simp) (Evaluates.lookup valid) Evaluates.constant
        simp [Mutable.getItem, sourceFound, Mutable.index, naturals, Except.map]
      refine ⟨digitObjects head++digitObjects item, ?_⟩
      simpa only [List.append_assoc] using Evaluates.call (.cons first (.cons (Evaluates.lookup getY) .nil))
        (is_permutation.result head item (middle++garbage)))
    (by simpa [invariant, comprehensionTargetsEnv, targetLocals] using getS)
  refine ⟨[.list (naturals tail)]++extra, ?_⟩
  simpa only [middle, List.append_assoc, ProjectEulerStatements.P49.allPerm] using checked

private abbrev lowerTest : Expr := .compare (.name "lower") [(.ltE, .name "a")]
private abbrev stepTest : Expr := .compare (.name "d") [(.gt, .constant (.int 0))]
private abbrev lastExpression : Expr := .subscript (.name "s") (.unaryOp .uSub (.constant (.int 1)))
private abbrev upperTest : Expr := .compare lastExpression [(.lt, .name "upper")]
private abbrev condition : Expr := .boolOp .and [lowerTest, stepTest, upperTest, primeAll, permutationAll]
private def accepts (lower upper a d length : Nat) : Bool :=
  decide (lower≤a ∧ 0<d ∧ a+(length-1)*d<upper) &&
    ProjectEulerStatements.P49.allPrime (ProjectEulerStatements.P49.seqFrom a d length) &&
    ProjectEulerStatements.P49.allPerm (ProjectEulerStatements.P49.seqFrom a d length)

private theorem condition_result (lower upper a d length : Nat) (positive : 0<length)
    (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]?=some (.list (naturals (ProjectEulerStatements.P49.seqFrom a d length))))
    (env : HeapCalls.Env) (getLower : env "lower"=some (number lower)) (getUpper : env "upper"=some (number upper))
    (getA : env "a"=some (number a)) (getD : env "d"=some (number d)) (getS : env "s"=some (.ref address)) :
    ∃ extra, Evaluates program env condition heap (flag (accepts lower upper a d length)) (heap++extra) := by
  have lowerValue : Evaluates program env lowerTest heap (flag (decide (lower≤a))) heap := by
    apply Evaluates.compare (Evaluates.lookup getLower) (Evaluates.lookup getA)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have stepValue : Evaluates program env stepTest heap (flag (decide (0<d))) heap := by
    apply Evaluates.compare (Evaluates.lookup getD) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have rowLength : (naturals (ProjectEulerStatements.P49.seqFrom a d length)).length=length := by
    simp [naturals, ProjectEulerStatements.P49.seqFrom]
  have lastItem : (naturals (ProjectEulerStatements.P49.seqFrom a d length))[length-1]?=
      some (number ((a+(length-1)*d : Nat) : Int)) := by
    simp [naturals, ProjectEulerStatements.P49.seqFrom, show length-1<length by omega]
  have adjusted : (-1+(length : Int)).toNat=length-1 := by omega
  have nonempty : naturals (ProjectEulerStatements.P49.seqFrom a d length) ≠ [] := by
    intro empty
    rw [empty, List.length_nil] at rowLength
    omega
  have lastRead : Evaluates program env lastExpression heap (number ((a+(length-1)*d : Nat) : Int)) heap := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup getS)
      (Evaluates.unary Evaluates.constant rfl)
    simp [Mutable.getItem, Mutable.index, found, rowLength, adjusted, nonempty, lastItem, Except.map]
  have upperValue : Evaluates program env upperTest heap (flag (decide (a+(length-1)*d<upper))) heap := by
    apply Evaluates.compare lastRead (Evaluates.lookup getUpper)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    simpa only [Int.natCast_add, Int.natCast_mul] using
      (Int.ofNat_lt : ((a+(length-1)*d : Nat) : Int)<(upper : Int) ↔ a+(length-1)*d<upper)
  have primesValue := prime_all (ProjectEulerStatements.P49.seqFrom a d length) heap address found env getS
  have permutationsValue : ∃ extra, Evaluates program env permutationAll heap
      (flag (ProjectEulerStatements.P49.allPerm (ProjectEulerStatements.P49.seqFrom a d length))) (heap++extra) := by
    have first : (ProjectEulerStatements.P49.seqFrom a d length)[0]?=some a := by
      simp [ProjectEulerStatements.P49.seqFrom, positive]
    cases row : ProjectEulerStatements.P49.seqFrom a d length with
    | nil => simp [row] at first
    | cons head tail =>
        simp only [row, List.getElem?_cons_zero, Option.some.injEq] at first
        subst head
        simpa only [row] using permutation_all a tail heap address (by simpa only [row] using found) env getS
  have tested := ProjectEulerSolutions.HeapTruthCollection.and_prefix program env heap
    [(lowerTest, decide (lower≤a)), (stepTest, decide (0<d)), (upperTest, decide (a+(length-1)*d<upper)),
      (primeAll, ProjectEulerStatements.P49.allPrime (ProjectEulerStatements.P49.seqFrom a d length))]
    permutationAll (ProjectEulerStatements.P49.allPerm (ProjectEulerStatements.P49.seqFrom a d length))
    (by
      intro expression value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · cases same; exact lowerValue
      · cases same; exact stepValue
      · cases same; exact upperValue
      · cases same; exact primesValue)
    permutationsValue
  simpa only [condition, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true, accepts, Bool.decide_and, Bool.and_assoc] using tested

private def Preserves (before after : Mutable.Heap) (collector : Nat) : Prop :=
  ∀ address object, address ≠ collector → before[address]?=some object → after[address]?=some object

private theorem Preserves.trans (first : Preserves before middle collector)
    (second : Preserves middle after collector) : Preserves before after collector :=
  fun address object other found => second address object other (first address object other found)

private theorem appended (heap extra : Mutable.Heap) (collector : Nat) : Preserves heap (heap++extra) collector :=
  fun _ _ _ found => ProjectEulerSolutions.HeapCollection.prefix_found heap extra _ _ found

private theorem updated (heap : Mutable.Heap) (collector : Nat) (object : Mutable.Object) :
    Preserves heap (heap.set collector object) collector := by
  intro address value other found
  simpa [List.getElem?_set_ne other.symm] using found

/-- The result retains the identities of accepted source sequence lists. -/
def Rows (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (rows : List (List Nat)) : Prop :=
  List.Forall₂ (fun address row => collector<address ∧ heap[address]?=some (.list (naturals row))) addresses rows

private theorem Rows.preserve {heap finalHeap : Mutable.Heap} {collector : Nat}
    {addresses : List Nat} {rows : List (List Nat)} (related : Rows heap collector addresses rows)
    (preserved : Preserves heap finalHeap collector) : Rows finalHeap collector addresses rows := by
  induction related with
  | nil => exact .nil
  | @cons address row addresses rows first rest ih =>
      exact .cons ⟨first.1, preserved address _ (by omega) first.2⟩ ih

private abbrev differenceBody : List Stmt :=
  [.assign [.name "s"] (.call (.name "seq_from") [.name "a", .name "d", .name "seqlen"]),
   .ifThen condition [.expr (.call (.attribute (.name "out") "append") [.name "s"])] []]

private def acceptedRow (lower upper a d length : Nat) : List (List Nat) :=
  if accepts lower upper a d length then [ProjectEulerStatements.P49.seqFrom a d length] else []

/-- One source iteration allocates its row even when an earlier Boolean guard rejects it. -/
private theorem difference_step (lower upper a d length : Nat) (positive : 0<length)
    (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (before : List (List Nat))
    (found : heap[collector]?=some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) (env : HeapCalls.Env)
    (getLower : env "lower"=some (number lower)) (getUpper : env "upper"=some (number upper))
    (getA : env "a"=some (number a)) (getD : env "d"=some (number d))
    (getLength : env "seqlen"=some (number length)) (getOut : env "out"=some (.ref collector)) :
    ∃ finalHeap finalAddresses,
      BlockContinues program env differenceBody heap (setLocal env "s" (.ref heap.length)) finalHeap ∧
      finalHeap[collector]?=some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before++acceptedRow lower upper a d length) ∧
      Preserves heap finalHeap collector := by
  let row := ProjectEulerStatements.P49.seqFrom a d length
  let initial := heap++[Mutable.Object.list (naturals row)]
  let bound := setLocal env "s" (.ref heap.length)
  have sequence : ReturnsValue program "seq_from" [number a, number d, number length]
      heap (.ref heap.length) initial := by
    simpa only [initial, row, naturals, numbers, progression_natural, Int.toNat_natCast,
      List.map_map, Function.comp_def] using seq_from.result a d length heap
  have assigned : BlockContinues program env
      [.assign [.name "s"] (.call (.name "seq_from") [.name "a", .name "d", .name "seqlen"])]
      heap bound initial := by
    exact BlockContinues.assign (Evaluates.call
      (.cons (Evaluates.lookup getA) (.cons (Evaluates.lookup getD) (.cons (Evaluates.lookup getLength) .nil))) sequence)
  obtain ⟨extra, tested⟩ := condition_result lower upper a d length positive initial heap.length
    (by simp [initial, row]) bound
    (by simpa [bound, setLocal] using getLower) (by simpa [bound, setLocal] using getUpper)
    (by simpa [bound, setLocal] using getA) (by simpa [bound, setLocal] using getD) (by simp [bound, setLocal])
  let expanded := initial++extra
  have kept : expanded[collector]?=some (.list (addresses.map Mutable.Value.ref)) :=
    ProjectEulerSolutions.HeapCollection.prefix_found initial extra collector _
      (ProjectEulerSolutions.HeapCollection.prefix_found heap _ collector _ found)
  have preserved : Preserves heap expanded collector := by
    simpa only [expanded, initial, List.append_assoc] using appended heap ([.list (naturals row)]++extra) collector
  cases accept : accepts lower upper a d length with
  | false =>
      refine ⟨expanded, addresses, ?_, kept, ?_, preserved⟩
      · apply assigned.append
        apply BlockContinues.branch (flag := false) (by simpa only [accept] using tested) rfl
        exact .nil
      · simpa only [acceptedRow, accept, Bool.false_eq_true, if_false, List.append_nil] using rows.preserve preserved
  | true =>
      let finalAddresses := addresses++[heap.length]
      let finalHeap := expanded.set collector (.list (finalAddresses.map Mutable.Value.ref))
      have inside : collector<heap.length := (List.getElem?_eq_some_iff.mp found).1
      have written : Preserves heap finalHeap collector := preserved.trans (updated expanded collector _)
      have emitted : BlockContinues program bound
          [.expr (.call (.attribute (.name "out") "append") [.name "s"])] expanded bound finalHeap := by
        apply BlockContinues.discard
        simpa only [finalHeap, finalAddresses, List.map_append, List.map_cons, List.map_nil] using
          Evaluates.append (Evaluates.lookup (by simpa [bound, setLocal] using getOut)) kept
            (Evaluates.lookup (by simp [bound, setLocal])) kept
      have fresh : collector<heap.length ∧ finalHeap[heap.length]?=some (.list (naturals row)) := by
        refine ⟨inside, ?_⟩
        rw [List.getElem?_set_ne (by omega : collector ≠ heap.length)]
        simp [expanded, initial, List.append_assoc]
      refine ⟨finalHeap, finalAddresses, ?_, ?_, ?_, written⟩
      · apply assigned.append
        apply BlockContinues.branch (flag := true) (by simpa only [accept] using tested) rfl
        exact emitted
      · apply List.getElem?_set_self
        simp only [expanded, initial, List.length_append, List.length_cons, List.length_nil]
        omega
      · simpa only [acceptedRow, accept, if_true] using
          List.rel_append (rows.preserve written) (List.Forall₂.cons fresh .nil)

private def Context (lower upper length collector : Nat) (env : HeapCalls.Env) : Prop :=
  env "lower"=some (number lower) ∧ env "upper"=some (number upper) ∧
    env "seqlen"=some (number length) ∧ env "out"=some (.ref collector)

private def differenceRows (lower upper a length first count : Nat) : List (List Nat) :=
  (List.range' first count).flatMap (fun d => acceptedRow lower upper a d length)

private theorem difference_loop (lower upper a length : Nat) (positive : 0<length)
    (count first stop : Nat) (bound : first+count=stop)
    (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (before : List (List Nat))
    (found : heap[collector]?=some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) (env : HeapCalls.Env)
    (context : Context lower upper length collector env) (getA : env "a"=some (number a)) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "d" first stop 1 differenceBody []] heap finalEnv finalHeap ∧
      Context lower upper length collector finalEnv ∧ finalEnv "a"=some (number a) ∧
      finalHeap[collector]?=some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before++differenceRows lower upper a length first count) ∧
      Preserves heap finalHeap collector := by
  induction count generalizing first heap addresses before env with
  | zero =>
      refine ⟨heap, env, addresses, ?_, context, getA, found, ?_, ?_⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
      · simpa [differenceRows] using rows
      · exact fun _ _ _ value => value
  | succ count ih =>
      let boundEnv := setLocal env "d" (number first)
      have nextContext : Context lower upper length collector boundEnv := by
        simpa [Context, boundEnv, setLocal] using context
      have nextA : boundEnv "a"=some (number a) := by simpa [boundEnv, setLocal] using getA
      obtain ⟨middle, middleAddresses, emitted, middleFound, middleRows, firstPreserved⟩ :=
        difference_step lower upper a first length positive heap collector addresses before found rows boundEnv
          nextContext.1 nextContext.2.1 nextA (by simp [boundEnv, setLocal]) nextContext.2.2.1 nextContext.2.2.2
      let middleEnv := setLocal boundEnv "s" (.ref heap.length)
      have middleContext : Context lower upper length collector middleEnv := by
        simpa [middleEnv, Context, setLocal] using nextContext
      have middleA : middleEnv "a"=some (number a) := by simpa [middleEnv, setLocal] using nextA
      obtain ⟨finalHeap, finalEnv, finalAddresses, rest, finalContext, finalA, finalFound, finalRows, restPreserved⟩ :=
        ih (first+1) (by omega) middle middleAddresses (before++acceptedRow lower upper a first length)
          middleFound middleRows middleEnv middleContext middleA
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalContext, finalA, finalFound, ?_, firstPreserved.trans restPreserved⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using emitted.append rest
      · simpa only [differenceRows, List.range'_succ, List.flatMap_cons, List.append_assoc] using finalRows

private abbrev startBody : List Stmt := [.forIn (.name "d") (.call (.name "range") [.name "upper"]) differenceBody []]
private def searchRows (lower upper length first count : Nat) : List (List Nat) :=
  (List.range' first count).flatMap (fun a => differenceRows lower upper a length 0 upper)

private theorem search_loop (lower upper length : Nat) (positive : 0<length)
    (count first stop : Nat) (bound : first+count=stop)
    (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (before : List (List Nat))
    (found : heap[collector]?=some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) (env : HeapCalls.Env)
    (context : Context lower upper length collector env) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "a" first stop 1 startBody []] heap finalEnv finalHeap ∧
      Context lower upper length collector finalEnv ∧
      finalHeap[collector]?=some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before++searchRows lower upper length first count) ∧
      Preserves heap finalHeap collector := by
  induction count generalizing first heap addresses before env with
  | zero =>
      refine ⟨heap, env, addresses, ?_, context, found, ?_, ?_⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
      · simpa [searchRows] using rows
      · exact fun _ _ _ value => value
  | succ count ih =>
      let boundEnv := setLocal env "a" (number first)
      have nextContext : Context lower upper length collector boundEnv := by
        simpa [Context, boundEnv, setLocal] using context
      obtain ⟨middle, middleEnv, middleAddresses, innerRun, middleContext, _, middleFound, middleRows, firstPreserved⟩ :=
        difference_loop lower upper first length positive upper 0 upper (by omega) heap collector addresses before found rows
          boundEnv nextContext (by simp [boundEnv, setLocal])
      have inner : BlockContinues program boundEnv startBody heap middleEnv middle := by
        apply BlockContinues.for_range (.cons (Evaluates.lookup nextContext.2.1) .nil) rfl
        exact innerRun
      obtain ⟨finalHeap, finalEnv, finalAddresses, rest, finalContext, finalFound, finalRows, restPreserved⟩ :=
        ih (first+1) (by omega) middle middleAddresses (before++differenceRows lower upper first length 0 upper)
          middleFound middleRows middleEnv middleContext
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalContext, finalFound, ?_, firstPreserved.trans restPreserved⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using inner.append rest
      · simpa only [searchRows, List.range'_succ, List.flatMap_cons, List.append_assoc] using finalRows

private theorem difference_fold (lower upper a length : Nat) (indices : List Nat) (tail : List (List Nat)) :
    indices.foldr (fun d acc => if accepts lower upper a d length then
      ProjectEulerStatements.P49.seqFrom a d length :: acc else acc) tail =
      (indices.flatMap (fun d => acceptedRow lower upper a d length))++tail := by
  induction indices with
  | nil => rfl
  | cons d indices ih =>
      simp only [List.foldr_cons, List.flatMap_cons, acceptedRow]
      split <;> simp_all [acceptedRow]

private theorem collect_fold (indices : List Nat) (select : Nat → List (List Nat)) (tail : List (List Nat)) :
    indices.foldr (fun a acc => select a++acc) tail=(indices.flatMap select)++tail := by
  induction indices with
  | nil => rfl
  | cons a indices ih => simp [ih, List.append_assoc]

private theorem searchRows_statement (n length : Nat) (positive : 0<n) (long : 2≤length) :
    searchRows (10^(n-1)) (10^n) length 0 (10^n)=ProjectEulerStatements.P49.naive n length := by
  unfold ProjectEulerStatements.P49.naive
  rw [dif_neg (by omega)]
  change searchRows (10^(n-1)) (10^n) length 0 (10^n) =
    (List.range (10^n)).foldr (fun a acc =>
      (List.range (10^n)).foldr (fun d acc2 => if accepts (10^(n-1)) (10^n) a d length then
        ProjectEulerStatements.P49.seqFrom a d length :: acc2 else acc2) acc) []
  simp_rw [difference_fold]
  rw [collect_fold]
  simp only [searchRows, differenceRows, List.range_eq_range', List.append_nil]

private abbrev initialEnv (n length : Int) : HeapCalls.Env :=
  functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number n, number length] []
private abbrev earlyGuard : Expr := .boolOp .or
  [.compare (.name "n") [(.eq, .constant (.int 0))],
   .compare (.name "seqlen") [(.lt, .constant (.int 2))]]

private theorem early_guard (n length : Int) (heap : Mutable.Heap) :
    Evaluates program (initialEnv n length) earlyGuard heap (flag (decide (n=0 ∨ length<2))) heap := by
  have first : Evaluates program (initialEnv n length)
      (.compare (.name "n") [(.eq, .constant (.int 0))]) heap (flag (decide (n=0))) heap := by
    exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
  have second : Evaluates program (initialEnv n length)
      (.compare (.name "seqlen") [(.lt, .constant (.int 2))]) heap (flag (decide (length<2))) heap := by
    exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
  by_cases zero : n=0
  · simp only [zero, true_or, decide_true]
    exact Evaluates.boolean_stop (by simpa only [zero, decide_true] using first) rfl rfl
  · simp only [zero, false_or]
    exact Evaluates.boolean_next (by simpa only [zero, decide_false] using first) rfl rfl
      (Evaluates.boolean_last second rfl)

/-- Short or zero-width inputs return a fresh empty result before evaluating powers. -/
theorem empty_result (n length : Int) (empty : n=0 ∨ length<2) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number n, number length] heap (.ref heap.length) (heap++[.list []]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true) (by simpa only [empty, decide_true] using early_guard n length heap) rfl
  exact BlockReturns.return_value (Evaluates.list .nil)

/-- The two finite source loops produce exactly the mathematical reference rows. -/
theorem result (n length : Nat) (positive : 0<n) (long : 2≤length) (heap : Mutable.Heap) :
    ∃ finalHeap addresses, ReturnsValue program "naive" [number n, number length]
      heap (.ref (heap.length+1)) finalHeap ∧
      finalHeap[heap.length+1]?=some (.list (addresses.map Mutable.Value.ref)) ∧
      Rows finalHeap (heap.length+1) addresses (ProjectEulerStatements.P49.naive n length) := by
  let lower : Nat := 10^(n-1)
  let upper : Nat := 10^n
  let initial := initialEnv n length
  let tupleHeap := heap++[Mutable.Object.tuple [number lower, number upper]]
  let tupleEnv := assignNames initial ["lower", "upper"] [number lower, number upper]
  let startHeap := tupleHeap++[Mutable.Object.list []]
  let startEnv := setLocal tupleEnv "out" (.ref tupleHeap.length)
  have exponent : Evaluates program initial (.binOp (.name "n") .sub (.constant (.int 1)))
      heap (number ((n-1 : Nat) : Int)) heap := by
    apply Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
    have minus : (n : Int)-1=((n-1 : Nat) : Int) := by omega
    simp [Mutable.binary, scalarBinary, number, minus]
  have lowerPower : Evaluates program initial
      (.binOp (.constant (.int 10)) .pow (.binOp (.name "n") .sub (.constant (.int 1)))) heap (number lower) heap := by
    apply Evaluates.binary Evaluates.constant exponent
    simp [Mutable.binary, scalarBinary, lower, number, show ¬ ((n-1 : Nat) : Int)<0 by omega]
  have upperPower : Evaluates program initial (.binOp (.constant (.int 10)) .pow (.name "n"))
      heap (number upper) heap := by
    apply Evaluates.binary Evaluates.constant (Evaluates.lookup rfl)
    simp [Mutable.binary, scalarBinary, upper, number, show ¬ (n : Int)<0 by omega]
  have tuple : Evaluates program initial (.tuple
      [.binOp (.constant (.int 10)) .pow (.binOp (.name "n") .sub (.constant (.int 1))),
       .binOp (.constant (.int 10)) .pow (.name "n")]) heap (.ref heap.length) tupleHeap :=
    Evaluates.tuple (.cons lowerPower (.cons upperPower .nil)) (by simp)
  have context : Context lower upper length tupleHeap.length startEnv := by
    have getLength : initial "seqlen"=some (number length) := rfl
    simpa [Context, startEnv, tupleEnv, assignNames, setLocal] using getLength
  obtain ⟨finalHeap, finalEnv, addresses, run, finalContext, found, rows, _⟩ :=
    search_loop lower upper length (by omega) upper 0 upper (by omega) startHeap tupleHeap.length [] []
      (by simp [startHeap]) .nil startEnv context
  have collected : Rows finalHeap (heap.length+1) addresses (ProjectEulerStatements.P49.naive n length) := by
    simpa only [List.nil_append, tupleHeap, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      lower, upper, searchRows_statement n length positive long] using rows
  refine ⟨finalHeap, addresses, ?_, ?_, collected⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (flag := false)
      (by simpa only [show ¬ ((n : Int)=0 ∨ (length : Int)<2) by omega, decide_false] using early_guard n length heap) rfl
    apply BlockReturns.unpack (items := [number lower, number upper]) (afterUnpack := tupleHeap) rfl tuple (by simp [Mutable.sequence, tupleHeap]) rfl
    apply BlockReturns.assign (Evaluates.list .nil)
    apply BlockContinues.returns (body := [.forIn (.name "a") (.call (.name "range") [.name "upper"]) startBody []])
    · apply BlockContinues.for_range (.cons (Evaluates.lookup context.2.1) .nil) rfl
      exact run
    · simpa only [tupleHeap, List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using
        BlockReturns.return_value (Evaluates.lookup finalContext.2.2.2)
  · simpa only [tupleHeap, List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using found

/-- Read an accepted row through the actual address stored in the output collector. -/
theorem Rows.at {heap : Mutable.Heap} {collector : Nat} {addresses : List Nat}
    {rows : List (List Nat)} {row : List Nat} (related : Rows heap collector addresses rows)
    (position : Nat) (item : rows[position]?=some row) :
    ∃ address, addresses[position]?=some address ∧ heap[address]?=some (.list (naturals row)) := by
  induction related generalizing position with
  | nil => simp at item
  | @cons address head addresses rows first rest ih =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at item
          subst row
          exact ⟨address, rfl, first.2⟩
      | succ position => exact ih position (by simpa using item)

private abbrev inputEnv (n : Int) : ScalarEnv :=
  fun name => if name="n" then some (.int n) else none

theorem «Returns» (n length : Int)
    (condition : Calls.Condition program (inputEnv n) P49Ast.requires_naive_0) :
    (HeapCalls.call program "naive" [number n, number length] []).Returns := by
  have nonnegative : 0≤n := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  by_cases empty : (n : Int)=0 ∨ length<2
  · exact (empty_result n length empty []).returns
  · lift length to Nat using (by omega : 0≤length)
    obtain ⟨finalHeap, addresses, executed, _, _⟩ := result n length (by omega) (by omega) []
    exact executed.returns

theorem «Supported» (n length : Int)
    (condition : Calls.Condition program (inputEnv n) P49Ast.requires_naive_0) :
    (HeapCalls.call program "naive" [number n, number length] []).Supported := («Returns» n length condition).supported

end naive

namespace naive_default
private def row (winner : Bool) : List Nat := if winner then [2969,6299,9629] else [1487,4817,8147]
private def exampleObject : Mutable.Object := .list (naive.naturals [1487,4817,8147])
private abbrev test : Expr := .compare (.name "seq") [(.notEq, .list
  [.constant (.int 1487), .constant (.int 4817), .constant (.int 8147)])]
private abbrev index (position : Int) : Expr := .subscript (.name "seq") (.constant (.int position))
private abbrev expression : Expr := .binOp
  (.binOp (.binOp (index 0) .mult (.binOp (.constant (.int 10)) .pow (.constant (.int 8)))) .add
    (.binOp (index 1) .mult (.binOp (.constant (.int 10)) .pow (.constant (.int 4))))) .add (index 2)
private abbrev body : List Stmt := [.ifThen test [.return expression] []]

private theorem unequal_int_lists (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (foundLeft : heap[a]?=some (.list (left.map fun n => .scalar (.int n))))
    (foundRight : heap[b]?=some (.list (right.map fun n => .scalar (.int n)))) (different : a≠b) :
    HeapCalls.compare .notEq (.ref a) (.ref b) heap =
      some (.ok (flag (decide (left≠right))), heap) := by
  simp [HeapCalls.compare, Mutable.array, foundLeft, foundRight, different, equalLists_ints]
  rfl

private theorem test_result (winner : Bool) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]?=some (.list (naive.naturals (row winner)))) (env : HeapCalls.Env)
    (getSeq : env "seq"=some (.ref address)) :
    Evaluates program env test heap (flag winner) (heap++[exampleObject]) := by
  have different : address ≠ heap.length := by have := (List.getElem?_eq_some_iff.mp found).1; omega
  have left : (heap++[exampleObject])[address]?=some (.list (naive.naturals (row winner))) :=
    ProjectEulerSolutions.HeapCollection.prefix_found heap [exampleObject] address _ found
  have right : (heap++[exampleObject])[heap.length]?=some exampleObject := by simp
  apply Evaluates.compare (av := .ref address) (bv := .ref heap.length)
    (middle := heap) (afterRight := heap++[exampleObject]) (Evaluates.lookup getSeq)
    (Evaluates.list (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
  have compared := unequal_int_lists ((row winner).map (fun (n : Nat) => (n : Int))) [1487,4817,8147]
    (heap++[exampleObject]) address heap.length
    (by simpa only [naive.naturals, List.map_map, Function.comp_def] using left)
    (by simpa only [exampleObject, naive.naturals, List.map_cons, List.map_nil] using right) different
  cases winner <;> simpa [row] using compared

private theorem expression_result (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]?=some (.list (naive.naturals [2969,6299,9629]))) (env : HeapCalls.Env)
    (getSeq : env "seq"=some (.ref address)) :
    Evaluates program env expression heap (number 296962999629) heap := by
  have first : Evaluates program env (index 0) heap (number 2969) heap := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup getSeq) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, found, naive.naturals, Except.map]
  have second : Evaluates program env (index 1) heap (number 6299) heap := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup getSeq) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, found, naive.naturals, Except.map]
  have third : Evaluates program env (index 2) heap (number 9629) heap := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup getSeq) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, found, naive.naturals, Except.map]
  have firstPart : Evaluates program env
      (.binOp (index 0) .mult (.binOp (.constant (.int 10)) .pow (.constant (.int 8))))
      heap (number 296900000000) heap :=
    Evaluates.binary first (Evaluates.binary Evaluates.constant Evaluates.constant rfl) rfl
  have secondPart : Evaluates program env
      (.binOp (index 1) .mult (.binOp (.constant (.int 10)) .pow (.constant (.int 4))))
      heap (number 62990000) heap :=
    Evaluates.binary second (Evaluates.binary Evaluates.constant Evaluates.constant rfl) rfl
  exact Evaluates.binary (Evaluates.binary firstPart secondPart rfl) third rfl

/-- The first reference row is skipped and the unique remaining row is concatenated. -/
theorem result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive_default" [] heap (number 296962999629) finalHeap := by
  obtain ⟨middle, addresses, searched, found, rows⟩ := naive.result 4 3 (by decide) (by decide) heap
  have actual : naive.Rows middle (heap.length+1) addresses [[1487,4817,8147],[2969,6299,9629]] := by
    simpa only [ProjectEulerSolutions.PrimePermutationReference.reference_rows] using rows
  obtain ⟨first, firstAt, firstFound⟩ := actual.at 0 rfl
  obtain ⟨second, secondAt, secondFound⟩ := actual.at 1 rfl
  let afterFirst := middle++[exampleObject]
  let afterSecond := afterFirst++[exampleObject]
  let initial := functionEnv ((findFunctionIn program.body "naive_default").getD ([], [])).1
    ((findFunctionIn program.body "naive_default").getD ([], [])).2 [] []
  let firstEnv := setLocal initial "seq" (.ref first)
  let secondEnv := setLocal firstEnv "seq" (.ref second)
  have firstTest := test_result false middle first firstFound firstEnv (by simp [firstEnv, setLocal])
  have secondFound' : afterFirst[second]?=some (.list (naive.naturals [2969,6299,9629])) :=
    ProjectEulerSolutions.HeapCollection.prefix_found middle [exampleObject] second _ secondFound
  have secondTest := test_result true afterFirst second secondFound' secondEnv (by simp [secondEnv, setLocal])
  have collectorFound : afterFirst[heap.length+1]?=some (.list (addresses.map Mutable.Value.ref)) :=
    ProjectEulerSolutions.HeapCollection.prefix_found middle [exampleObject] (heap.length+1) _ found
  have finalFound : afterSecond[second]?=some (.list (naive.naturals [2969,6299,9629])) :=
    ProjectEulerSolutions.HeapCollection.prefix_found afterFirst [exampleObject] second _ secondFound'
  refine ⟨afterSecond, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_sequence (items := addresses.map Mutable.Value.ref)
    (by intro expressions; simp)
    (Evaluates.call (.cons Evaluates.constant (.cons Evaluates.constant .nil)) searched)
    (by simp [Mutable.sequence, found])
  apply BlockReturns.sequence_step (items := addresses.map Mutable.Value.ref) (value := .ref first)
    (by simp [sequenceValue, sequenceSource, Mutable.sequence, found]) (by simp [firstAt])
  apply BlockReturns.branch (flag := false) firstTest rfl
  change BlockReturns program firstEnv
    [.sequenceStepLoop "seq" (.ref (heap.length+1)) 1 body [], .return (.constant (.int 0))]
    afterFirst (number 296962999629) afterSecond
  apply BlockReturns.sequence_step (items := addresses.map Mutable.Value.ref) (value := .ref second)
    (by simp [sequenceValue, Mutable.sequence, collectorFound])
    (by simp [secondAt])
  apply BlockReturns.branch (flag := true) secondTest rfl
  exact BlockReturns.return_value (expression_result afterSecond second finalFound secondEnv (by simp [secondEnv, setLocal]))

theorem «Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨finalHeap, executed⟩ := result []
  exact executed.scalar_returns

theorem «Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported := «Returns».supported

end naive_default

end data.«project-euler-statements».data.py.project_euler_statements.p49
