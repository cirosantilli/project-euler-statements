import data.«project-euler-statements».data.py.project_euler_statements.«p81.py.lean.d».Row

namespace data.«project-euler-statements».data.py.project_euler_statements.p81
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P81
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev lastOrZero (name : String) : Expr :=
  .ifExp (.name name) (.subscript (.name name) (.unaryOp .uSub (.constant (.int 1)))) (.constant (.int 0))

theorem lastOrZero_result (heap : Mutable.Heap) (env : HeapCalls.Env) (name : String)
    (address : Nat) (values : List Int)
    (contents : heap[address]? = some (.list (encode values)))
    (localValue : env name = some (.ref address)) :
    Evaluates program env (lastOrZero name) heap (number (values.getLast?.getD 0)) heap := by
  by_cases empty : values = []
  · subst values
    exact Evaluates.conditional (flag := false) (Evaluates.lookup localValue)
      (by simp [Mutable.truth, contents, encode]) Evaluates.constant
  · apply Evaluates.conditional (flag := true) (Evaluates.lookup localValue)
      (by simp [Mutable.truth, contents, encode, empty])
    have positive : 0 < values.length := List.length_pos_iff.mpr empty
    have tail : values[values.length - 1]? = some (values.getLast?.getD 0) := by
      rw [List.getLast?_eq_getElem?]
      simp [List.getElem?_eq_getElem (by omega : values.length - 1 < values.length)]
    apply Evaluates.subscript (by intros a b c impossible; cases impossible)
      (Evaluates.lookup localValue) (Evaluates.unary Evaluates.constant rfl)
    have offset : ((-1 : Int) + values.length).toNat = values.length - 1 := by omega
    simp [Mutable.getItem, Mutable.index, contents, encode, number, offset, tail, Except.map,
      show ¬ (-1 : Int) + values.length < 0 by omega,
      show ¬ (values.length : Int) ≤ -1 + values.length by omega]

abbrev prefixBody : List Stmt :=
  [.expr (.call (.attribute (.name "init") "append") [.binOp (.name "x") .add (lastOrZero "init")])]

def prefixHeap (base : Mutable.Heap) (output : List Int) : Mutable.Heap := base ++ [.list (encode output)]

theorem prefixLoop_result (base : Mutable.Heap) (env : HeapCalls.Env) (address position : Nat)
    (row output : List Int) (contents : base[address]? = some (.list (encode row)))
    (localInit : env "init" = some (.ref base.length)) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "x" (.ref address) position prefixBody []] (prefixHeap base output) finalEnv
      (prefixHeap base (output ++ firstRowFrom (output.getLast?.getD 0) (row.drop position))) ∧
      ∀ name, name ≠ "x" → finalEnv name = env name := by
  have source : Mutable.sequence (sequenceValue (.ref address)) (prefixHeap base output) =
      some (.ok (encode row), prefixHeap base output) := by
    have found : (prefixHeap base output)[address]? = some (.list (encode row)) := by
      unfold prefixHeap
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp contents).1]
      exact contents
    simp [sequenceValue, Mutable.sequence, found]
  by_cases active : position < row.length
  · let x := row[position]
    let value := output.getLast?.getD 0 + x
    let entered := setLocal env "x" (number x)
    have getInit : entered "init" = some (.ref base.length) := by simpa [entered, setLocal] using localInit
    have found : (prefixHeap base output)[base.length]? = some (.list (encode output)) := by simp [prefixHeap]
    have computed : Evaluates program entered (.binOp (.name "x") .add (lastOrZero "init"))
        (prefixHeap base output) (number value) (prefixHeap base output) := by
      apply Evaluates.binary (Evaluates.lookup rfl) (lastOrZero_result _ entered "init" base.length output found getInit)
      simp [Mutable.binary, scalarBinary, number, value, Int.add_comm]
    have appended := Evaluates.append (globals := []) (module := program) (Evaluates.lookup getInit) found computed found
    have write : (prefixHeap base output).set base.length (.list (encode output ++ [number value])) =
        prefixHeap base (output ++ [value]) := by simp [prefixHeap, encode, number]
    rw [write] at appended
    obtain ⟨finalEnv, continued, kept⟩ := prefixLoop_result base entered address (position + 1) row (output ++ [value]) contents getInit
    have next : output ++ firstRowFrom (output.getLast?.getD 0) (row.drop position) =
        (output ++ [value]) ++ firstRowFrom ((output ++ [value]).getLast?.getD 0) (row.drop (position + 1)) := by
      rw [List.drop_eq_getElem_cons active]
      simp [firstRowFrom, value, x, List.append_assoc]
    refine ⟨finalEnv, ?_, ?_⟩
    · rw [next]
      apply BlockContinues.sequence_step (value := number x) source (by simp [encode, List.getElem?_eq_getElem active, x, number])
      simpa [prefixBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using
        (BlockContinues.discard appended).append continued
    · intro name different
      rw [kept name different]
      simp [entered, setLocal, different]
  · have gone : row.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨env, ?_, by intros; rfl⟩
    simp only [gone, firstRowFrom, List.append_nil]
    exact BlockContinues.sequence_done source (by simp [encode, List.getElem?_eq_none (by omega : row.length ≤ position)]) BlockContinues.nil
termination_by row.length - position
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p81
