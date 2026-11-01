import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Consecutive
import ProjectEulerSolutions.Lib.RationalIntegers
import lang.py.FormalSW.BooleanCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

abbrev program := P93Ast.module
abbrev positiveTest : Expr := .compare (.name "numerator") [(.gt, .constant (.int 0))]
abbrev divisibleTest : Expr :=
  .compare (.binOp (.name "numerator") .mod (.name "denominator")) [(.eq, .constant (.int 0))]
abbrev quotient : Expr := .binOp (.name "numerator") .floorDiv (.name "denominator")
abbrev emit : List Stmt := [.expr (.call (.attribute (.name "integers") "append") [quotient])]
abbrev filterBody : List Stmt := [.ifThen (.boolOp .and [positiveTest, divisibleTest]) emit []]
abbrev orderBody : List Stmt :=
  [.forIn (.tuple [.name "numerator", .name "denominator"])
    (.call (.name "all_results") [.name "order"]) filterBody []]

theorem source_body : ((findFunctionIn program.body "consecutive_for_digits").getD ([], [])).2 =
    [.assign [.name "integers"] (.list []),
     .forIn (.name "order") (.permutationsIterable [.name "digits", .constant .none]) orderBody [],
     .return (.call (.name "consecutive_count") [.name "integers"])] := rfl

/-- The source guard retains Python's short-circuit order and exact signed remainder. -/
theorem filter_test (pair : Pair) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (positive : 0 < pair.2)
    (getN : env "numerator" = some (Heap.number pair.1))
    (getD : env "denominator" = some (Heap.number pair.2)) :
    EvaluatesTruth program env (.boolOp .and [positiveTest, divisibleTest]) heap
      (decide (0 < pair.1 ∧ pair.1 % pair.2 = 0)) globals := by
  have first : EvaluatesTruth program env positiveTest heap (decide (0 < pair.1)) globals := by
    refine ⟨.scalar (.bool (decide (0 < pair.1))), ?_, rfl⟩
    exact Evaluates.compare (Evaluates.lookup getN) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  have second : EvaluatesTruth program env divisibleTest heap (decide (pair.1 % pair.2 = 0)) globals := by
    refine ⟨.scalar (.bool (decide (pair.1 % pair.2 = 0))), ?_, rfl⟩
    apply Evaluates.compare
      (Evaluates.binary (value := Heap.number (pair.1 % pair.2)) (finalHeap := heap)
        (Evaluates.lookup getN) (Evaluates.lookup getD)
        (by simp [Mutable.binary, scalarBinary, positive, positive.ne'])) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  simpa only [Bool.decide_and] using first.and second

/-- One iteration appends an exact positive integer or leaves the collector untouched. -/
theorem filter_result (base : Mutable.Heap) (old : List Int) (garbage : Mutable.Heap)
    (pair : Pair) (env : HeapCalls.Env) (globals : Mutable.Globals) (positive : 0 < pair.2)
    (getOut : env "integers" = some (.ref base.length))
    (getN : env "numerator" = some (Heap.number pair.1))
    (getD : env "denominator" = some (Heap.number pair.2)) :
    BlockContinues program env filterBody (working base (old.map Heap.number) garbage) env
      (working base ((old ++ integerResult pair).map Heap.number) garbage) globals := by
  obtain ⟨test, evaluated, truth⟩ := filter_test pair (working base (old.map Heap.number) garbage)
    env globals positive getN getD
  by_cases accepted : 0 < pair.1 ∧ pair.1 % pair.2 = 0
  · simp only [integerResult, if_pos accepted, List.map_append, List.map_cons, List.map_nil]
    apply BlockContinues.branch (flag := true) evaluated (by simpa [accepted] using truth)
    have divided : Evaluates program env quotient (working base (old.map Heap.number) garbage)
        (Heap.number (pair.1 / pair.2)) (working base (old.map Heap.number) garbage) globals :=
      Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup getD)
        (by simp [Mutable.binary, scalarBinary, positive, positive.ne'])
    have appended := Evaluates.append (Evaluates.lookup getOut) (found base (old.map Heap.number) garbage)
      divided (found base (old.map Heap.number) garbage)
    simpa only [store] using BlockContinues.discard appended
  · simp only [integerResult, if_neg accepted, List.append_nil]
    exact BlockContinues.branch (flag := false) evaluated (by simpa only [accepted, decide_false] using truth) .nil

/-- Live tuple unpacking and collection preserve all input pairs and other caller objects. -/
theorem filter_loop (base : Mutable.Heap) (address : Nat) (values : List Mutable.Value)
    (different : base.length ≠ address) (remaining : List Pair) (pending : List Mutable.Value)
    (position : Nat) (old : List Int) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals)
    (foundList : (working base (old.map Heap.number) garbage)[address]? = some (.list values))
    (suffix : values.drop position = pending)
    (todo : Heap.Rows (working base (old.map Heap.number) garbage) pending remaining)
    (positive : ∀ pair ∈ remaining, 0 < pair.2)
    (getOut : env "integers" = some (.ref base.length)) :
    ∃ finalEnv,
      BlockContinues program env
        [.unpackStepLoop ["numerator", "denominator"] (.ref address) position filterBody []]
        (working base (old.map Heap.number) garbage) finalEnv
        (working base ((old ++ integerResults remaining).map Heap.number) garbage) globals ∧
      (∀ name, name ≠ "numerator" → name ≠ "denominator" → finalEnv name = env name) := by
  induction remaining generalizing pending position old env with
  | nil =>
    cases todo
    refine ⟨env, ?_, fun _ _ _ => rfl⟩
    simp only [integerResults, List.flatMap_nil, List.append_nil]
    apply BlockContinues.unpack_done (items := values)
      (by simp [sequenceValue, Mutable.sequence, foundList]) (rest := .nil)
    have atHead := congrArg (fun xs : List Mutable.Value => xs[0]?) suffix
    simpa using atHead
  | cons pair remaining ih =>
    cases todo with
    | cons row tail =>
      rename_i head pending
      obtain ⟨pairAddress, rfl, foundPair⟩ := row
      let bound := assignNames env ["numerator", "denominator"] [Heap.number pair.1, Heap.number pair.2]
      have keptOut : bound "integers" = some (.ref base.length) := by
        simpa [bound, assignNames, setLocal] using getOut
      have emitted := filter_result base old garbage pair bound globals (positive pair (by simp)) keptOut
        (by simp [bound, assignNames, setLocal]) (by simp [bound, assignNames, setLocal])
      have keptList : (working base ((old ++ integerResult pair).map Heap.number) garbage)[address]? =
          some (.list values) := by
        simpa only [List.append_nil] using
          other_found base (old.map Heap.number) ((old ++ integerResult pair).map Heap.number)
            garbage [] address (.list values) different foundList
      have nextSuffix : values.drop (position + 1) = pending := by
        simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail suffix
      have keptRows : Heap.Rows (working base ((old ++ integerResult pair).map Heap.number) garbage)
          pending remaining := by
        simpa only [List.append_nil] using
          Heap.Rows.collector tail ((old ++ integerResult pair).map Heap.number) []
      obtain ⟨finalEnv, continued, unchanged⟩ := ih pending (position + 1) (old ++ integerResult pair) bound
        keptList nextSuffix keptRows (fun pair member => positive pair (by simp [member])) keptOut
      refine ⟨finalEnv, ?_, ?_⟩
      · apply BlockContinues.unpack_step (items := values) (value := .ref pairAddress)
          (values := [Heap.number pair.1, Heap.number pair.2])
          (by simp [sequenceValue, Mutable.sequence, foundList])
        · have atHead := congrArg (fun xs : List Mutable.Value => xs[0]?) suffix
          simpa using atHead
        · simp [Mutable.sequence, foundPair, Heap.object]
        · rfl
        · simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, integerResults, List.flatMap_cons,
            List.append_assoc] using emitted.append continued
      · intro name notN notD
        exact (unchanged name notN notD).trans (by simp [bound, assignNames, setLocal, notN, notD])

end data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits
