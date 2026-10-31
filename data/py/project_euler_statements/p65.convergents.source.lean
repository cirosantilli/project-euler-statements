import data.«project-euler-statements».data.py.project_euler_statements.«p65.coefficients.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p65
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.EConvergents
set_option Elab.async false
private abbrev program := P65Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (values : List Nat) := values.map number
variable {globals : Mutable.Globals}

private def recurrence : List Stmt :=
  [.assign [.tuple [.name "p0", .name "p1"]]
    (.tuple [.name "p1", .binOp (.binOp (.name "a") .mult (.name "p1")) .add (.name "p0")])]

private theorem recurrence_loop (values remaining : List Nat) (position older current : Nat)
    (suffix : values.drop position = remaining) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers values))) (env : HeapCalls.Env)
    (getOlder : env "p0" = some (number older)) (getCurrent : env "p1" = some (number current)) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "a" (.ref address) position recurrence [], .return (.name "p1")]
      heap (number (run remaining older current)) (heap ++ extra) globals := by
  have sequence : Mutable.sequence (.ref address) heap = some (.ok (numbers values), heap) := by
    simp [Mutable.sequence, found]
  induction remaining generalizing position older current heap env with
  | nil =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.sequence_done (source := .ref address) sequence
      · have exhausted : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [numbers, exhausted]
      · exact BlockReturns.return_value (Evaluates.lookup getCurrent)
  | cons value rest ih =>
      let entered := setLocal env "a" (number value)
      let pair := [number current, number (value * current + older)]
      let middle := heap ++ [.tuple pair]
      let ready := assignNames entered ["p0", "p1"] pair
      have preserved : middle[address]? = some (.list (numbers values)) := by
        simpa only [middle, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found
      obtain ⟨extra, continued⟩ := ih (position + 1) current (value * current + older)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) middle preserved ready
        (by simp [ready, pair, assignNames, setLocal]) (by simp [ready, pair, assignNames, setLocal])
        (by simp [Mutable.sequence, preserved])
      refine ⟨[.tuple pair] ++ extra, ?_⟩
      have item : values[position]? = some value := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockReturns.sequence_step (source := .ref address) (value := number value) sequence
        (by simp [numbers, item])
      apply BlockReturns.unpack (names := ["p0", "p1"]) (items := pair) (middle := middle) (afterUnpack := middle) rfl
      · apply Evaluates.tuple (values := pair)
        · refine .cons (Evaluates.lookup (by simpa [entered, setLocal] using getCurrent)) (.cons ?_ .nil)
          apply Evaluates.binary (av := number (value * current)) (bv := number older)
            (middle := heap) (afterRight := heap)
          · exact Evaluates.binary (av := number value) (bv := number current)
              (middle := heap) (afterRight := heap)
              (Evaluates.lookup (by simp [setLocal]))
              (Evaluates.lookup (by simpa [entered, setLocal] using getCurrent))
              (by simp [Mutable.binary, scalarBinary, number])
          · exact Evaluates.lookup (by simpa [entered, setLocal] using getOlder)
          · simp [Mutable.binary, scalarBinary, number]
        · simp [pair]
      · simp [Mutable.sequence, middle]
      · rfl
      · simpa only [Calls.loopContinuation, show Calls.loopControl recurrence = false from rfl,
          Bool.false_eq_true, if_false, middle, List.append_assoc, run_cons] using continued

/-- Tuple swapping consumes the allocated coefficient list without altering it. -/
theorem convergent_num.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "convergent_num" [number n] heap
      (number (numerator n)) (heap ++ extra) globals := by
  let args := ((findFunctionIn program.body "convergent_num").getD ([], [])).1
  let body := ((findFunctionIn program.body "convergent_num").getD ([], [])).2
  let env := functionEnv args body [number n] globals
  let initial := heap ++ [.tuple [number 0, number 1]]
  let withCoefficients := initial ++ [.list (numbers (coefficients n))]
  let ready := assignNames env ["p0", "p1"] [number 0, number 1]
  obtain ⟨extra, executed⟩ := recurrence_loop (globals := globals) (coefficients n) (coefficients n) 0 0 1 rfl
    withCoefficients initial.length (by simp [withCoefficients]) ready
    (by simp [ready, assignNames, setLocal]) (by simp [ready, assignNames, setLocal])
  refine ⟨[.tuple [number 0, number 1], .list (numbers (coefficients n))] ++ extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := ["p0", "p1"]) (items := [number 0, number 1])
    (middle := initial) (afterUnpack := initial) rfl
  · exact Evaluates.tuple (.cons Evaluates.constant (.cons Evaluates.constant .nil)) (by simp)
  · simp [Mutable.sequence, initial]
  · rfl
  · apply BlockReturns.for_sequence (items := numbers (coefficients n)) (middle := withCoefficients)
      (by intro expressions; simp)
      (Evaluates.call (.cons (Evaluates.lookup (by simpa [ready, assignNames, setLocal] using
        (show env "n" = some (number n) from by cases globals <;> rfl))) .nil)
        (coeffs.result n initial globals))
      (by simp [Mutable.sequence, withCoefficients])
    simpa only [withCoefficients, initial, List.append_assoc, List.cons_append, List.nil_append, numerator] using executed

end data.«project-euler-statements».data.py.project_euler_statements.p65
