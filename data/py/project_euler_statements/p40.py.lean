import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p40.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerStatements.Lib.ChampernownePrefix
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
  change Calls.Extends { body := program.body.take 3 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digit_at", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
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


namespace digit_at
open ProjectEulerStatements.ChampernowneBlocks ProjectEulerStatements.ChampernownePrefix
private def condition : Expr := .compare (.builtinCall .len [.name "digits"]) [(.lt, .name "n")]
private def body : List Stmt :=
  [.augAssign (.name "digits") .add (.call (.name "digits_be") [.name "value"]),
   .augAssign (.name "value") .add (.constant (.int 1))]
private def finish : Stmt := .return (.subscript (.name "digits") (.binOp (.name "n") .sub (.constant (.int 1))))
private def current (base extra : Mutable.Heap) (count : Nat) : Mutable.Heap :=
  base ++ .list (numbers (champernowneDigits count)) :: extra

private theorem loop (n count : Nat) (positive : 0 < n) (base extra : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getDigits : env "digits" = some (.ref base.length))
    (getValue : env "value" = some (number (count + 1))) :
    ∃ finalExtra, BlockReturns program env [.whileDo condition body [], finish]
      (current base extra count) (number (blockDigit 1 n)) (base ++ finalExtra) := by
  have found : (current base extra count)[base.length]? = some (.list (numbers (champernowneDigits count))) := by
    simp [current]
  have tested : Evaluates program env condition (current base extra count)
      (.scalar (.bool (decide ((champernowneDigits count).length < n)))) (current base extra count) := by
    apply Evaluates.compare (av := number (champernowneDigits count).length) (bv := number n)
      (middle := current base extra count) (afterRight := current base extra count)
    · exact Evaluates.builtin (.cons (Evaluates.lookup getDigits) .nil)
        (by simp [primitive, Mutable.length, found, numbers])
    · exact Evaluates.lookup getN
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases short : (champernowneDigits count).length < n
  · let updated := setLocal env "digits" (.ref base.length)
    let advanced := setLocal updated "value" (number (count + 2))
    have appended : BlockContinues program env [body[0]'(by decide)] (current base extra count)
        updated (current base (extra ++ digitHeap (count + 1)) (count + 1)) := by
      apply BlockContinues.augAssign (left := .ref base.length)
        (right := .ref ((current base extra count).length + 1)) getDigits
      · exact Evaluates.call (.cons (Evaluates.lookup getValue) .nil) (digits_result (count + 1) _)
      · have left := found_append found (digitHeap (count + 1))
        have right : ((current base extra count) ++ digitHeap (count + 1))[(current base extra count).length + 1]? =
            some (.list (numbers (digitsBE (count + 1)))) := by simp [digitHeap]
        rw [inplace_add_lists _ _ _ _ _ left right]
        simp [current, numbers, ProjectEulerStatements.ChampernownePrefix.succ, List.map_append, List.append_assoc]
    have incremented : BlockContinues program updated [body[1]'(by decide)]
        (current base (extra ++ digitHeap (count + 1)) (count + 1)) advanced
        (current base (extra ++ digitHeap (count + 1)) (count + 1)) := by
      apply BlockContinues.augAssign (left := number (count + 1))
        (right := number 1) (by simpa [updated, setLocal] using getValue) Evaluates.constant
      simp [inplace, Mutable.binary, scalarBinary, number, Int.add_assoc]
    obtain ⟨finalExtra, rest⟩ := loop n (count + 1) positive base (extra ++ digitHeap (count + 1)) advanced
      (by simpa [advanced, updated, setLocal] using getN)
      (by simp [advanced, updated, setLocal]) (by simp [advanced, setLocal, Nat.add_assoc])
    refine ⟨finalExtra, ?_⟩
    apply BlockReturns.while_loop (flag := true) (by simpa only [short, decide_true] using tested) rfl
    have ran := appended.append incremented
    simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_or,
      Bool.false_eq_true, if_false, List.append_assoc, List.nil_append, List.append_nil] using ran.returns rest
  · refine ⟨.list (numbers (champernowneDigits count)) :: extra, ?_⟩
    apply BlockReturns.while_loop (flag := false) (by simpa only [short, decide_false] using tested) rfl
    apply BlockReturns.return_value
    apply Evaluates.subscript (position := number (n - 1)) (middle := current base extra count)
      (afterIndex := current base extra count) (finalHeap := current base extra count)
      (by intros; simp) (Evaluates.lookup getDigits)
      (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number, Int.natCast_sub (by omega : 1 ≤ n)]))
    have inside : n - 1 < (champernowneDigits count).length := by omega
    have read := Mutable.getItem_list (current base extra count) base.length (n - 1)
      (numbers (champernowneDigits count)) found (by simpa only [numbers, List.length_map] using inside)
    have digit : (champernowneDigits count)[n - 1] = blockDigit 1 n :=
      (List.getD_eq_getElem _ _ inside).symm.trans (digit_complete n count positive (by omega))
    simpa only [numbers, List.getElem_map, digit] using read
termination_by n - (champernowneDigits count).length
decreasing_by
  have contributes := digits_positive (count + 1) (by omega)
  rw [ProjectEulerStatements.ChampernownePrefix.succ, List.length_append]
  omega

/-- The source grows its digit buffer until the requested position exists, preserving caller objects. -/
theorem result (n : Nat) (positive : 0 < n) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "digit_at" [number n] heap (number (blockDigit 1 n)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "digit_at").getD ([], [])).1
    ((findFunctionIn program.body "digit_at").getD ([], [])).2 [number n] []
  let ready := setLocal (setLocal initial "digits" (.ref heap.length)) "value" (number 1)
  obtain ⟨extra, returned⟩ := loop n 0 positive heap [] ready
    (by simp [ready, setLocal]; rfl) (by simp [ready, setLocal]) (by simp [ready, setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := heap)
    (Evaluates.compare (Evaluates.lookup (show initial "n" = some (number n) from rfl)) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, show n ≠ 0 by omega])) rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply BlockReturns.assign Evaluates.constant
  exact returned

end digit_at

namespace naive
open ProjectEulerStatements.ChampernowneBlocks
private def body : List Stmt := [.augAssign (.name "product") .mult (.call (.name "digit_at") [.name "position"])]
def answer (positions : List Nat) : Nat := positions.foldl (fun total position => total * blockDigit 1 position) 1

private theorem loop (items remaining : List Nat) (position address total : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (found : heap[address]? = some (.tuple (numbers items))) (suffix : items.drop position = remaining)
    (positive : ∀ n ∈ remaining, 0 < n) (getTotal : env "product" = some (number total)) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "position" (.ref address) position body [], .return (.name "product")]
      heap (number (remaining.foldl (fun total n => total * blockDigit 1 n) total)) (heap ++ extra) := by
  induction remaining generalizing position total env heap with
  | nil =>
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      apply BlockReturns.sequence_done (source := .ref address) (items := numbers items)
        (by simp [sequenceValue, Mutable.sequence, found])
      · have missing : items[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        simp [numbers, missing]
      · exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | cons head tail ih =>
      have item : items[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      let bound := setLocal env "position" (number head)
      let updated := setLocal bound "product" (number (total * blockDigit 1 head))
      have boundTotal : bound "product" = some (number total) := by simpa [bound, setLocal] using getTotal
      obtain ⟨firstExtra, digit⟩ := digit_at.result head (positive head (by simp)) heap
      have tailSuffix : items.drop (position + 1) = tail := by simp [List.drop_add_one_eq_tail_drop, suffix]
      obtain ⟨restExtra, rest⟩ := ih (position + 1) (total * blockDigit 1 head) (heap ++ firstExtra) updated
        (found_append found firstExtra) tailSuffix (fun n member => positive n (by simp [member])) rfl
      refine ⟨firstExtra ++ restExtra, ?_⟩
      apply BlockReturns.sequence_step (source := .ref address) (items := numbers items) (value := number head)
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [numbers, item])
      apply BlockReturns.augAssign (left := number total) (right := number (blockDigit 1 head))
        (value := number (total * blockDigit 1 head)) (middle := heap ++ firstExtra)
        (afterOperation := heap ++ firstExtra) boundTotal
      · exact Evaluates.call (.cons (Evaluates.lookup (show bound "position" = some (number head) from rfl)) .nil) digit
      · simp [inplace, Mutable.binary, scalarBinary, number]
      · simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_or,
          Bool.false_eq_true, if_false, List.nil_append, List.foldl_cons, List.append_assoc] using rest

/-- Any finite tuple of positive positions has the stated product, with all caller objects preserved. -/
theorem result (positions : List Nat) (positive : ∀ n ∈ positions, 0 < n) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.tuple (numbers positions))) :
    ∃ extra, ReturnsValue program "naive" [.ref address] heap (number (answer positions)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [.ref address] []
  let ready := setLocal initial "product" (number 1)
  obtain ⟨extra, returned⟩ := loop positions positions 0 address 1 heap ready found rfl positive rfl
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_sequence (items := numbers positions) (value := .ref address)
    (by intros; simp) (Evaluates.lookup (show ready "positions" = some (.ref address) from rfl))
    (by simp [Mutable.sequence, found])
  exact returned

end naive

end data.«project-euler-statements».data.py.project_euler_statements.p40
