import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».ChoiceExecution
import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».Display
import lang.py.FormalSW.HeapMemoLoopRules

/-! The reference counts each suffix while retaining all existing input objects. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.counting
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
open choose_faces (Row)
set_option Elab.async false

abbrev spec := expand69.pool.spec

theorem cache_disjoint : HeapMemoCalls.CacheDisjoint program program := by
  intro name cached
  change name ∈ ([] : List String) at cached
  simp at cached

structure Required where
  pairs : List can_show.Pair
  address : Nat

def Required.Valid (required : Required) (heap : Mutable.Heap) : Prop :=
  heap[required.address]? = some (.list (required.pairs.map can_show.Pair.reference)) ∧
    ∀ pair ∈ required.pairs, pair.Valid heap

theorem Required.Valid.append {required : Required} {heap : Mutable.Heap}
    (valid : required.Valid heap) (extra : Mutable.Heap) : required.Valid (heap ++ extra) :=
  ⟨HeapCollection.prefix_found heap extra _ _ valid.1,
    fun pair member => HeapCollection.prefix_found heap extra _ _ (valid.2 pair member)⟩

theorem row_valid_append (row : Row) (heap extra : Mutable.Heap) (valid : row.Valid heap) :
    row.Valid (heap ++ extra) := HeapCollection.prefix_found heap extra _ _ valid

def test (required : Required) (left right : Row) : Bool :=
  displays left.labels right.labels (required.pairs.map can_show.Pair.model)

def code : List Stmt :=
  match findFunctionIn program.body "naive" with
  | some (_, body) => executableBody body
  | none => []

def outerBody : List Stmt :=
  match (code[2]? : Option Stmt) with
  | some (.forIn _ _ body _) => body
  | _ => []

def innerBody : List Stmt :=
  match (outerBody[0]? : Option Stmt) with
  | some (.forIn _ _ body _) => body
  | _ => []

/-- Only the current right die and accumulated count are assigned in the inner loop. -/
def Keep (before after : HeapCalls.Env) : Prop :=
  ∀ name, name ≠ "b" → name ≠ "pairs" → after name = before name

/-- The body calls the actual reference predicate, sharing its live compiler tuple cache. -/
theorem checked (required : Required) (left right : Row) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (valid : required.Valid heap) (leftValid : left.Valid heap) (rightValid : right.Valid heap)
    (getLeft : env "a" = some left.reference) (getRight : env "b" = some right.reference)
    (getRequired : env "required_pairs" = some (.ref required.address)) :
    HeapMemoCalls.EvaluatesRel program spec env
      (.call (.name "can_show") [.name "a", .name "b", .name "required_pairs"]) heap
      (fun value after => value = .scalar (.bool (test required left right)) ∧ ∃ extra, after = heap ++ extra) globals := by
  apply HeapMemoCalls.EvaluatesRel.call
    (HeapMemoCalls.ArgumentsRel.fixed (.cons (HeapMemoCalls.Evaluates.lookup getLeft)
      (.cons (HeapMemoCalls.Evaluates.lookup getRight) (.cons (HeapMemoCalls.Evaluates.lookup getRequired) .nil))))
  rintro values middle ⟨rfl, rfl⟩
  exact can_show.result left.labels right.labels left.address right.address required.address required.pairs _ globals
    leftValid rightValid valid.1 valid.2

/-- All suffix positions contribute independently; the continuation sees the updated count and preserved locals. -/
theorem row_loop (required : Required) (left : Row) (rows remaining : List Row)
    (address position count : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (following : List Stmt) (post : Mutable.Value → Mutable.Heap → Prop)
    (valid : required.Valid heap) (leftValid : left.Valid heap)
    (rowsValid : ∀ row ∈ remaining, row.Valid heap)
    (found : heap[address]? = some (.list (rows.map Row.reference)))
    (suffix : rows.drop position = remaining)
    (getLeft : env "a" = some left.reference) (getRequired : env "required_pairs" = some (.ref required.address))
    (getCount : env "pairs" = some (number count))
    (continued : ∀ extra afterEnv, afterEnv "pairs" = some (number (count + remaining.countP (test required left))) →
      Keep env afterEnv → HeapMemoCalls.BlockReturnsRel program spec afterEnv following (heap ++ extra) post globals) :
    HeapMemoCalls.BlockReturnsRel program spec env
      (.sequenceStepLoop "b" (.ref address) position innerBody [] :: following) heap post globals := by
  induction remaining generalizing position count heap env with
  | nil =>
      apply HeapMemoCalls.BlockReturnsRel.sequence_done (items := rows.map Row.reference)
        (by simp [sequenceValue, Mutable.sequence, found])
      · have missing : rows[position]? = none := List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp suffix)
        simp [missing]
      · simpa using continued [] env (by simpa using getCount) (by intro name _ _; rfl)
  | cons row rest ih =>
      have item : rows[position]? = some row := by
        simpa [suffix] using (List.head?_drop (l := rows) (i := position)).symm
      have tail : rows.drop (position + 1) = rest := by simp [List.drop_add_one_eq_tail_drop, suffix]
      let bound := setLocal env "b" row.reference
      have tested := checked required left row heap bound globals valid leftValid (rowsValid row (by simp))
        (by simpa [bound, setLocal] using getLeft) rfl (by simpa [bound, setLocal] using getRequired)
      apply HeapMemoCalls.BlockReturnsRel.sequence_step (items := rows.map Row.reference) (value := row.reference)
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [item])
      apply HeapMemoCalls.BlockReturnsRel.branch tested
      rintro value after ⟨rfl, extra, rfl⟩
      refine ⟨test required left row, rfl, ?_⟩
      have resume (next : Nat) (nextEnv : HeapCalls.Env)
          (total : next + rest.countP (test required left) = count + (row :: rest).countP (test required left))
          (nextCount : nextEnv "pairs" = some (number next)) (kept : Keep env nextEnv) :
          HeapMemoCalls.BlockReturnsRel program spec nextEnv
            (.sequenceStepLoop "b" (.ref address) (position + 1) innerBody [] :: following) (heap ++ extra) post globals := by
        apply ih (position := position + 1) (count := next) (heap := heap ++ extra) (env := nextEnv)
          (valid.append extra) (row_valid_append left heap extra leftValid)
          (fun row member => row_valid_append row heap extra (rowsValid row (by simp [member])))
          (HeapCollection.prefix_found heap extra address _ found) tail
          (by rw [kept "a" (by decide) (by decide)]; exact getLeft)
          (by rw [kept "required_pairs" (by decide) (by decide)]; exact getRequired) nextCount
        intro more finalEnv finalCount finalKept
        simpa only [List.append_assoc] using continued (extra ++ more) finalEnv
          (by simpa only [total] using finalCount)
          (by intro name notB notPairs; exact (finalKept name notB notPairs).trans (kept name notB notPairs))
      cases accepted : test required left row with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
          apply resume count bound
          · simp [accepted]
          · simpa [bound, setLocal] using getCount
          · intro name notB _; simp [bound, setLocal, notB]
      | true =>
          simp only [↓reduceIte]
          apply HeapMemoCalls.BlockReturnsRel.augAssign
            (by simpa [bound, setLocal] using getCount) HeapMemoCalls.Evaluates.constant.rel
          rintro value middle ⟨rfl, rfl⟩
          refine ⟨number (count + 1), _, rfl, (by intro cache holds; exact holds), ?_⟩
          apply resume (count + 1) (setLocal bound "pairs" (number (count + 1)))
          · simp [accepted, Nat.add_assoc, Nat.add_comm]
          · rfl
          · intro name notB notPairs; simp [bound, setLocal, notB, notPairs]

end data.«project-euler-statements».data.py.project_euler_statements.p90.counting
