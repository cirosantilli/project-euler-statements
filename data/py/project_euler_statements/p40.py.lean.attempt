import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p40.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerStatements.P40
import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p40
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.P40
private abbrev program := P40Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number
private abbrev digitHeap (n : Nat) : Mutable.Heap :=
  [.list (numbers (Nat.digits 10 n)), .list (numbers (digitsBE n))]

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["champernowne_digits", "digit_at", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem digits_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digits_be" [number n] heap (.ref (heap.length + 1))
      (heap ++ digitHeap n) := by
  apply ReturnsValue.with_defaults rfl rfl rfl
  simpa [digitHeap, digitsBE, numbers, number, List.map_reverse] using
    (common.digits_be.result n 10 (by decide) heap).extend common_extension

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

namespace champernowne_digits
private abbrev body : List Stmt :=
  [.augAssign (.name "out") .add (.call (.name "digits_be")
    [.binOp (.name "i") .add (.constant (.int 1))])]
private def collect (count start : Nat) (items : List Nat) : List Nat :=
  (List.range' start count).foldl (fun acc i => acc ++ digitsBE (i + 1)) items

private theorem iteration (base extra : Mutable.Heap) (items : List Nat) (i : Nat)
    (env : HeapCalls.Env) (getI : env "i" = some (number i))
    (getOut : env "out" = some (.ref base.length)) :
    BlockContinues program env body (base ++ .list (numbers items) :: extra)
      (setLocal env "out" (.ref base.length))
      (base ++ .list (numbers (items ++ digitsBE (i + 1))) ::
        (extra ++ digitHeap (i + 1))) := by
  let current := base ++ .list (numbers items) :: extra
  apply BlockContinues.augAssign (left := .ref base.length)
    (right := .ref (current.length + 1)) getOut
  · exact Evaluates.call (.cons (Evaluates.binary (Evaluates.lookup getI) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number, current])) .nil) (digits_result (i + 1) current)
  · have left : (current ++ digitHeap (i + 1))[base.length]? = some (.list (numbers items)) := by
      simp [current, List.append_assoc]
    have right : (current ++ digitHeap (i + 1))[current.length + 1]? =
        some (.list (numbers (digitsBE (i + 1)))) := by simp [digitHeap]
    rw [inplace_add_lists _ _ _ _ _ left right]
    simp [current, numbers, List.map_append, List.append_assoc]

private theorem loop (limit count start : Nat) (bound : start + count = limit)
    (base extra : Mutable.Heap) (items : List Nat) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) (getOut : env "out" = some (.ref base.length)) :
    ∃ finalEnv finalExtra,
      BlockContinues program env [.rangeStepLoop "i" start limit 1 body []]
        (base ++ .list (numbers items) :: extra) finalEnv
        (base ++ .list (numbers (collect count start items)) :: finalExtra) ∧
      finalEnv "limit" = some (number limit) ∧ finalEnv "out" = some (.ref base.length) := by
  induction count generalizing start extra items env with
  | zero =>
      refine ⟨env, extra, ?_, getLimit, getOut⟩
      apply BlockContinues.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockContinues.nil
  | succ count ih =>
      let boundEnv := setLocal env "i" (number start)
      let nextEnv := setLocal boundEnv "out" (.ref base.length)
      have ran := iteration base extra items start boundEnv rfl
        (by simp [boundEnv, setLocal, getOut])
      obtain ⟨finalEnv, finalExtra, rest, finalLimit, finalOut⟩ :=
        ih (start + 1) (by omega) (extra ++ digitHeap (start + 1))
          (items ++ digitsBE (start + 1)) nextEnv
          (by simp [nextEnv, boundEnv, setLocal, getLimit]) rfl
      refine ⟨finalEnv, finalExtra, ?_, finalLimit, finalOut⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        collect, List.range'_succ] using ran.append rest

/-- The collector keeps its identity while every digits_be call allocates its two lists. -/
theorem result (limit : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "champernowne_digits" [number limit] heap (.ref heap.length)
      (heap ++ .list (numbers (champernowneDigits limit)) :: extra) := by
  let initial := functionEnv ((findFunctionIn program.body "champernowne_digits").getD ([], [])).1
    ((findFunctionIn program.body "champernowne_digits").getD ([], [])).2 [number limit] []
  let ready := setLocal initial "out" (.ref heap.length)
  obtain ⟨finalEnv, extra, executed, _, finalOut⟩ := loop limit limit 0 (by omega)
    heap [] [] ready rfl rfl
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply BlockReturns.for_range (.cons (Evaluates.lookup rfl) .nil) rfl
  simpa [collect, champernowneDigits, List.range_eq_range'] using
    executed.returns (BlockReturns.return_value (rest := []) (Evaluates.lookup finalOut))

end champernowne_digits

namespace digit_at
private abbrev indexExpr : Expr := .binOp (.name "n") .sub (.constant (.int 1))
private abbrev guard : Expr :=
  .compare (.constant (.int 0)) [(.ltE, indexExpr), (.lt, .builtinCall .len [.name "ds"])]

private theorem index_result (n : Nat) (positive : 0 < n) (env : HeapCalls.Env)
    (heap : Mutable.Heap) (getN : env "n" = some (number n)) :
    Evaluates program env indexExpr heap (number (n - 1)) heap :=
  Evaluates.binary (Evaluates.lookup getN) Evaluates.constant
    (by simp [Mutable.binary, scalarBinary, number, Int.natCast_sub (by omega : 1 ≤ n)])

private theorem guard_result (n : Nat) (positive : 0 < n) (items : List Nat)
    (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getDs : env "ds" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    Evaluates program env guard heap (.scalar (.bool (decide (n - 1 < items.length)))) heap := by
  apply Evaluates.chain Evaluates.constant
  apply Evaluates.Compares.next (compared := .scalar (.bool true)) (afterComparison := heap)
    (index_result n positive env heap getN)
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  · rfl
  · apply Evaluates.Compares.last (value := number items.length) (middle := heap)
    · exact Evaluates.builtin (.cons (Evaluates.lookup getDs) .nil)
        (by simp [primitive, Mutable.length, found, numbers, number])
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

/-- The helper uses one-based indexing; zero is deliberately outside this correspondence. -/
theorem result (n limit : Nat) (positive : 0 < n) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "digit_at" [number n, number limit] heap
      (number (digitAt n limit)) (heap ++ extra) := by
  obtain ⟨extra, collected⟩ := champernowne_digits.result limit heap
  let items := champernowneDigits limit
  let finalHeap := heap ++ .list (numbers items) :: extra
  let initial := functionEnv ((findFunctionIn program.body "digit_at").getD ([], [])).1
    ((findFunctionIn program.body "digit_at").getD ([], [])).2 [number n, number limit] []
  let ready := setLocal initial "ds" (.ref heap.length)
  have found : finalHeap[heap.length]? = some (.list (numbers items)) := by simp [finalHeap]
  have tested := guard_result n positive items finalHeap heap.length ready rfl rfl found
  refine ⟨.list (numbers items) :: extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) collected)
  apply BlockReturns.return_value
  by_cases inside : n - 1 < items.length
  · apply Evaluates.conditional (flag := true) (value := .scalar (.bool true))
      (by simpa [inside] using tested) rfl
    apply Evaluates.subscript (by intros; simp [indexExpr]) (Evaluates.lookup rfl)
      (index_result n positive ready finalHeap rfl)
    have selected : digitAt n limit = items[n - 1] :=
      List.getD_eq_getElem _ _ inside
    change Mutable.getItem (.ref heap.length) (number (n - 1)) finalHeap =
      some (.ok (number (digitAt n limit)), finalHeap)
    rw [selected]
    have read := Mutable.getItem_list finalHeap heap.length (n - 1) (numbers items) found
      (by simpa only [numbers, List.length_map] using inside)
    have mapped : (numbers items)[n - 1]'(by simpa only [numbers, List.length_map] using inside) =
        number items[n - 1] := List.getElem_map number
    rw [mapped] at read
    exact read
  · have empty : digitAt n limit = 0 := by
      simp [digitAt, items, show items.length ≤ n - 1 by omega]
    rw [empty]
    apply Evaluates.conditional (flag := false) (value := .scalar (.bool false))
      (by simpa [inside] using tested) rfl
    exact Evaluates.constant

end digit_at
namespace naive
private def positions : List Nat := [1, 10, 100, 1000, 10000, 100000, 1000000]
private abbrev loopBody : List Stmt :=
  [.augAssign (.name "acc") .mult (.call (.name "digit_at") [.name "i", .name "limit"])]

private theorem loop (items remaining : List Nat) (position address total limit : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (found : heap[address]? = some (.list (numbers items)))
    (suffix : items.drop position = remaining)
    (positive : ∀ n ∈ remaining, 0 < n)
    (getLimit : env "limit" = some (number limit))
    (getTotal : env "acc" = some (number total)) :
    ∃ finalHeap, BlockReturns program env
      [.sequenceStepLoop "i" (.ref address) position loopBody [], .return (.name "acc")]
      heap (number (remaining.foldl (fun acc n => acc * digitAt n limit) total)) finalHeap := by
  induction remaining generalizing position total env heap with
  | nil =>
      refine ⟨heap, ?_⟩
      have sequence : Mutable.sequence (.ref address) heap = some (.ok (numbers items), heap) := by
        simp [Mutable.sequence, found]
      apply BlockReturns.sequence_done (source := .ref address) sequence
      · have missing : items[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        simp [numbers, missing]
      · exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | cons head tail ih =>
      have item : items[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      let bound := setLocal env "i" (number head)
      have getI : bound "i" = some (number head) := by simp [bound, setLocal]
      have boundLimit : bound "limit" = some (number limit) := by
        simpa [bound, setLocal] using getLimit
      have boundTotal : bound "acc" = some (number total) := by
        simpa [bound, setLocal] using getTotal
      obtain ⟨extra, digit⟩ := digit_at.result head limit (positive head (by simp)) heap
      let nextEnv := setLocal bound "acc" (number (total * digitAt head limit))
      have tailSuffix : items.drop (position+1) = tail := by
        simp [List.drop_add_one_eq_tail_drop, suffix]
      obtain ⟨finalHeap, rest⟩ := ih (position+1) (total*digitAt head limit) (heap++extra) nextEnv
        (found_append found extra) tailSuffix (fun n member => positive n (by simp [member]))
        (by simpa [nextEnv, setLocal] using boundLimit) rfl
      refine ⟨finalHeap, ?_⟩
      have sequence : Mutable.sequence (.ref address) heap = some (.ok (numbers items), heap) := by
        simp [Mutable.sequence, found]
      apply BlockReturns.sequence_step (source := .ref address) (value := number head)
        sequence (by simp [numbers, item])
      apply BlockReturns.augAssign (left := number total) (right := number (digitAt head limit))
        (value := number (total*digitAt head limit)) (middle := heap++extra)
        (afterOperation := heap++extra) boundTotal
      · exact Evaluates.call (.cons (Evaluates.lookup getI) (.cons (Evaluates.lookup boundLimit) .nil)) digit
      · simp [inplace, Mutable.binary, scalarBinary, number]
      · simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, List.foldl_cons] using rest

/-- Each digit lookup constructs its actual finite stream; none is evaluated as a certificate. -/
theorem result (limit : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [number limit] heap
      (number (ProjectEulerStatements.P40.naive limit)) finalHeap := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let ready := setLocal initial "acc" (number 1)
  let allocated := heap ++ [.list (numbers positions)]
  obtain ⟨finalHeap, returned⟩ := loop positions positions 0 heap.length 1 limit allocated ready
    (by simp [allocated]) rfl
    (by intro n member; simp only [positions, List.mem_cons, List.not_mem_nil, or_false] at member; omega)
    (by change initial "limit" = some (number limit); rfl) rfl
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_sequence (items := numbers positions)
    (by intros; simp)
    (Evaluates.list (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant
        (.cons Evaluates.constant .nil))))))))
    (by simp [Mutable.sequence, numbers, positions])
  exact returned

theorem «Returns» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P40Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have nonnegative : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift limit to Nat using nonnegative
  obtain ⟨_, returned⟩ := result limit []
  exact returned.scalar_returns

theorem «Supported» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P40Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  («Returns» limit condition).supported
end naive

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive_default" [] heap
      (number (ProjectEulerStatements.P40.naive 1000000)) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.result 1000000 heap
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons Evaluates.constant .nil) returned)

theorem naive_default.«Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨_, returned⟩ := naive_default.result []
  exact ReturnsValue.scalar_returns (values := []) returned

theorem naive_default.«Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p40
