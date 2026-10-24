import data.«project-euler-statements».data.py.project_euler_statements.«p68.scan.source»
import ProjectEulerSolutions.Lib.HeapCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p68
open FormalSW.PyAst HeapCalls ProjectEulerStatements MagicRing MagicRingTextCalls
set_option Elab.async false

abbrev integer (value : Int) : Mutable.Value := .scalar (.int value)
abbrev referenceArgs : List Arg := ((findFunctionIn program.body "naive").getD ([], [])).1
abbrev referenceBody : List Stmt := ((findFunctionIn program.body "naive").getD ([], [])).2
abbrev guardExpression : Expr := .boolOp .or
  [.compare (.name "n") [(.lt, .constant (.int 3))],
   .compare (.name "digits") [(.lt, .binOp (.constant (.int 3)) .mult (.name "n"))]]
abbrev labelsExpression : Expr :=
  .listComp (.name "$formalsw.range.item")
    [("$formalsw.range.item", .call (.name "range") [.constant (.int 1),
      .binOp (.binOp (.constant (.int 2)) .mult (.name "n")) .add (.constant (.int 1))], [])]
abbrev referenceCode : List Stmt :=
  [.ifThen guardExpression [.return (.constant (.string ""))] [],
   .assign [.name "best"] (.constant (.string "")),
   .forIn (.name "values") (.permutationsIterable [labelsExpression, .constant .none])
     permutationBody [], .return (.name "best")]

theorem reference_function_source :
    findFunctionIn program.body "naive" = some (referenceArgs, referenceBody) := rfl

theorem reference_code_source : executableBody referenceBody = referenceCode := rfl

theorem guard_result (n digits : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (integer n)) (getDigits : env "digits" = some (integer digits)) :
    Evaluates program env guardExpression heap
      (.scalar (.bool (decide (n < 3 ∨ digits < 3 * n)))) heap := by
  have low : Evaluates program env (.compare (.name "n") [(.lt, .constant (.int 3))]) heap
      (.scalar (.bool (decide (n < 3)))) heap :=
    Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup getN) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  have short : Evaluates program env
      (.compare (.name "digits") [(.lt, .binOp (.constant (.int 3)) .mult (.name "n"))]) heap
      (.scalar (.bool (decide (digits < 3 * n)))) heap := by
    exact Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup getDigits)
      (Evaluates.binary (middle := heap) (afterRight := heap) (value := integer (3 * n))
        Evaluates.constant (Evaluates.lookup getN) rfl)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases small : n < 3
  · simpa only [small, true_or, decide_true] using
      (Evaluates.boolean_stop (op := .or)
        (rest := [.compare (.name "digits")
          [(.lt, .binOp (.constant (.int 3)) .mult (.name "n"))]])
        (by simpa only [small, decide_true] using low) rfl rfl)
  · change Evaluates program env (.boolOp .or _) heap _ heap
    apply Evaluates.boolean_next (flag := false)
      (by simpa only [small, decide_false] using low) rfl rfl
    simpa only [small, false_or] using Evaluates.boolean_last short rfl

theorem labels_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    ∃ extra, Evaluates program env labelsExpression heap (.ref heap.length)
      (heap ++ (.list (encode (labels n)) :: extra)) := by
  obtain ⟨extra, collected⟩ := ProjectEulerSolutions.HeapCollection.range_map (globals := [])
    program "$formalsw.range.item" (.name "$formalsw.range.item") number
    (fun heap env value found => ⟨[], by simpa using
      (Evaluates.lookup (module := program) (heap := heap) found)⟩)
    heap env [.constant (.int 1),
      .binOp (.binOp (.constant (.int 2)) .mult (.name "n")) .add (.constant (.int 1))]
    [number 1, number (2 * n + 1)] 1 (2 * n)
    (.cons Evaluates.constant (.cons
      (Evaluates.binary (av := number (2 * n)) (bv := number 1)
        (middle := heap) (afterRight := heap)
        (Evaluates.binary (middle := heap) (afterRight := heap)
          Evaluates.constant (Evaluates.lookup getN)
          (by simp [Mutable.binary, scalarBinary, number])) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) .nil))
    (by change Except.ok (ε := ExceptionObject) ((1 : Int), ((2 * n + 1 : Nat) : Int), (1 : Int)) =
          .ok (1, (1 : Int) + ((2 * n : Nat) : Int), 1)
        simp only [Int.natCast_add, Int.natCast_one, Int.add_comm])
  exact ⟨extra, by simpa only [labelsExpression, labels, encode,
    ProjectEulerSolutions.HeapCollection.working] using collected⟩

theorem positive_result (n digits : Nat) (size : 3 ≤ n) (width : 3 * n ≤ digits)
    (heap : Mutable.Heap) (values : List Mutable.Value)
    (arguments : completeArguments referenceArgs values = some [number n, number digits]) :
    ∃ finalHeap, ReturnsValue program "naive" values heap
      (string (referenceAnswer n digits)) finalHeap := by
  let env := HeapCalls.argumentEnv referenceArgs [number n, number digits]
  let readyEnv := setLocal env "best" (string "")
  have ready : SearchReady n digits "" readyEnv := by
    constructor <;> rfl
  obtain ⟨extra, pooled⟩ := labels_result n heap readyEnv ready.getN
  let poolHeap := heap ++ (.list (encode (labels n)) :: extra)
  have acquired : permutationRows [.ref heap.length, .scalar .none] poolHeap =
      some (.ok (capturedRows (Permutations.rows (2 * n) (labels n))), poolHeap) := by
    have fromList := permutationRows_list poolHeap heap.length (encode (labels n))
      (by simp [poolHeap])
    simpa only [capturedRows, encode, List.length_map, labels, List.length_range',
      Permutations.rows_map, List.map_map, Function.comp_def] using fromList
  have assignments : ∀ row ∈ Permutations.rows (2 * n) (labels n), row.Perm (labels n) := by
    intro row member
    apply Permutations.mem_rows_full_iff.mp
    simpa only [labels, List.length_range'] using member
  obtain ⟨finalHeap, scanned⟩ := permutations_result n (by omega) digits
    (Permutations.rows (2 * n) (labels n)) assignments "" poolHeap readyEnv ready
  rw [referenceScan_answer] at scanned
  have tested := guard_result n digits heap env rfl rfl
  have guarded : ¬ ((n : Int) < 3 ∨ (digits : Int) < 3 * n) := by omega
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function reference_function_source arguments
  rw [reference_code_source]
  apply BlockReturns.branch (flag := false) (by simpa only [guarded, decide_false] using tested) rfl
  apply BlockReturns.assign Evaluates.constant
  exact BlockReturns.for_permutations
    (.cons pooled (.cons Evaluates.constant .nil)) acquired scanned

theorem naive.result (n digits : Int) (heap : Mutable.Heap) (values : List Mutable.Value)
    (arguments : completeArguments referenceArgs values = some [integer n, integer digits]) :
    ∃ finalHeap, ReturnsValue program "naive" values heap
      (string (referenceResult n digits)) finalHeap := by
  by_cases rejected : n < 3 ∨ digits < 3 * n
  · refine ⟨heap, ?_⟩
    have tested := guard_result n digits heap
      (HeapCalls.argumentEnv referenceArgs [integer n, integer digits]) rfl rfl
    apply BlockReturns.function reference_function_source arguments
    rw [reference_code_source]
    apply BlockReturns.branch (flag := true)
      (by simpa only [rejected, decide_true] using tested) rfl
    simpa only [referenceResult, if_pos rejected] using
      (BlockReturns.return_value (module := program) (value := string "") Evaluates.constant)
  · have nCast : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
    have digitsCast : (digits.toNat : Int) = digits := Int.toNat_of_nonneg (by omega)
    have size : 3 ≤ n.toNat := by omega
    have width : 3 * n.toNat ≤ digits.toNat := by omega
    obtain ⟨finalHeap, executed⟩ := positive_result n.toNat digits.toNat size width heap values
      (by simpa only [number, nCast, digitsCast, integer] using arguments)
    exact ⟨finalHeap, by simpa only [referenceResult, if_neg rejected, number,
      nCast, digitsCast, integer] using executed⟩

theorem naive.full_result (n digits : Int) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [integer n, integer digits] heap
      (string (referenceResult n digits)) finalHeap := naive.result n digits heap _ rfl

theorem naive.one_argument_result (n : Int) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [integer n] heap
      (string (referenceResult n 16)) finalHeap := naive.result n 16 heap _ rfl

theorem naive.default_result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [] heap
      (string (referenceResult 5 16)) finalHeap := naive.result 5 16 heap _ rfl

end data.«project-euler-statements».data.py.project_euler_statements.p68
