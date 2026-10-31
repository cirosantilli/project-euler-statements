import data.«project-euler-statements».data.py.project_euler_statements.«p79.validation.source»

/-! The complete reference body for stable sequence inputs, including validation and cycles. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

/-- The caller's input remains readable when the reference allocates private lists. -/
structure SequenceInput (base : Mutable.Heap) (source : SequenceSource)
    (attempts : List String) : Prop where
  read : ∀ heap, base <+: heap →
    Mutable.sequence (sequenceValue source) heap = some (.ok (attempts.map text), heap)

theorem SequenceInput.list (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.list (attempts.map text))) :
    SequenceInput base (.ref address) attempts := by
  constructor
  intro heap saved
  obtain ⟨suffix, rfl⟩ := saved
  have retained : (base ++ suffix)[address]? = some (.list (attempts.map text)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simp [sequenceValue, Mutable.sequence, retained]

theorem SequenceInput.tuple (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.tuple (attempts.map text))) :
    SequenceInput base (.ref address) attempts := by
  constructor
  intro heap saved
  obtain ⟨suffix, rfl⟩ := saved
  have retained : (base ++ suffix)[address]? = some (.tuple (attempts.map text)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simp [sequenceValue, Mutable.sequence, retained]

def validatedOutcome (checked : List String) : List String → Except ExceptionObject Mutable.Value
  | [] => checkedOutcome checked
  | s :: rest =>
      if s.length = 3 ∧ Strings.isDigit s = true then validatedOutcome (checked ++ [s]) rest
      else .error (invalidException s)

theorem validatedOutcome_prefix (checked accepted rest : List String)
    (valid : ∀ s ∈ accepted, s.length = 3 ∧ Strings.isDigit s = true) :
    validatedOutcome checked (accepted ++ rest) = validatedOutcome (checked ++ accepted) rest := by
  induction accepted generalizing checked with
  | nil => simp
  | cons s tail ih =>
      have head := valid s (by simp)
      have later : ∀ s ∈ tail, s.length = 3 ∧ Strings.isDigit s = true :=
        fun s member => valid s (List.mem_cons_of_mem _ member)
      simp only [List.cons_append, validatedOutcome, if_pos head,
        ih _ later, List.append_assoc, List.nil_append]

theorem validatedOutcome_valid (attempts : List String)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true) :
    validatedOutcome [] attempts = checkedOutcome attempts := by
  simpa only [List.append_nil, List.nil_append, validatedOutcome] using
    validatedOutcome_prefix [] attempts [] valid

theorem validatedOutcome_first_error (accepted rest : List String) (s : String)
    (valid : ∀ s ∈ accepted, s.length = 3 ∧ Strings.isDigit s = true)
    (invalid : ¬ (s.length = 3 ∧ Strings.isDigit s = true)) :
    validatedOutcome [] (accepted ++ s :: rest) = .error (invalidException s) := by
  rw [validatedOutcome_prefix [] accepted (s :: rest) valid]
  simp only [validatedOutcome, if_neg invalid]

theorem validation_enter (base : Mutable.Heap) (source : SequenceSource)
    (attempts before rest : List String) (s : String)
    (input : SequenceInput base source attempts) (partition : attempts = before ++ s :: rest)
    (heap : Mutable.Heap) (saved : base <+: heap) (env : HeapCalls.Env)
    (following : List Stmt) (anchors : Nat) (stack : List Frame) :
    Reaches program anchors
      ⟨.block ([validationLoop source before.length] ++ following) env, stack, heap⟩
      ⟨.block (validationBody ++ ([validationLoop source (before.length + 1)] ++ following))
        (setLocal env "attempt" (text s)), stack, heap⟩ := by
  have item : (attempts.map text)[before.length]? = some (text s) := by simp [partition]
  exact .next (by
    simp [validationLoop, step, run, input.read heap saved, item, List.append_assoc]
    rfl) .refl

theorem validated_sequence (base : Mutable.Heap) (source : SequenceSource)
    (attempts : List String) (input : SequenceInput base source attempts)
    (remaining before checked : List String) (partition : attempts = before ++ remaining)
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref base.length)) :
    ∃ after, SourceResult
      (.block [validationLoop source before.length, .return checkedExpression] env)
      (base ++ [.list (checked.map text)]) (validatedOutcome checked remaining) after ∧
      base <+: after := by
  induction remaining generalizing before checked env with
  | nil =>
      obtain ⟨after, returned, saved⟩ := checked_return_result
        (base ++ [.list (checked.map text)]) base.length checked (by simp) env getChecked
      refine ⟨after, ?_, (List.prefix_append _ _).trans saved⟩
      apply SourceResult.before _ _ _ _ _ _ _ returned
      intro anchors stack
      have noItem : (attempts.map text)[before.length]? = none := by simp [partition]
      exact .next (by simp [validationLoop, step, run,
        input.read _ (List.prefix_append _ _), noItem]) .refl
  | cons s rest ih =>
      let bound := setLocal env "attempt" (text s)
      have boundChecked : bound "checked" = some (.ref base.length) := by
        simpa [bound, setLocal] using getChecked
      have boundAttempt : bound "attempt" = some (text s) := by simp [bound, setLocal]
      have entered := validation_enter base source attempts before rest s input partition
        (base ++ [.list (checked.map text)]) (List.prefix_append _ _) env
        [.return checkedExpression]
      by_cases valid : s.length = 3 ∧ Strings.isDigit s = true
      · simp only [validatedOutcome, if_pos valid]
        obtain ⟨after, continued, saved⟩ := ih (before ++ [s]) (checked ++ [s])
          (by simpa [List.append_assoc] using partition) bound boundChecked
        have iteration := accepted_attempt base checked bound s boundChecked boundAttempt
          valid.1 valid.2
        refine ⟨after, ?_, saved⟩
        apply SourceResult.before _ _ _ _ _ _ _
          (show SourceResult
            (.block [validationLoop source (before.length + 1), .return checkedExpression] bound)
            (base ++ [.list ((checked ++ [s]).map text)])
            (validatedOutcome (checked ++ [s]) rest) after from by simpa using continued)
        intro anchors stack
        exact (entered anchors stack).trans
          (iteration [validationLoop source (before.length + 1), .return checkedExpression]
            anchors stack)
      · simp only [validatedOutcome, if_neg valid]
        refine ⟨base ++ [.list (checked.map text)], ?_, List.prefix_append _ _⟩
        apply SourceResult.before _ _ _ _ _ _ entered
        apply rejected_attempt bound _ s boundAttempt
        by_cases length : s.length = 3
        · exact Or.inr (by simpa [length] using valid)
        · exact Or.inl length

theorem naive_body_result (base : Mutable.Heap) (value : Mutable.Value)
    (attempts : List String) (input : SequenceInput base (sequenceSource value) attempts)
    (env : HeapCalls.Env) (getInput : env "attempts" = some value) :
    ∃ after, SourceResult (.block naiveCode env) base (validatedOutcome [] attempts) after ∧
      base <+: after := by
  let bound := setLocal env "checked" (.ref base.length)
  let heap := base ++ [.list []]
  obtain ⟨after, result, saved⟩ := validated_sequence base (sequenceSource value) attempts input
    attempts [] [] rfl bound (by simp [bound, setLocal])
  refine ⟨after, ?_, saved⟩
  apply SourceResult.before _ _ _ _ _ _ _ result
  intro anchors stack
  rw [naive_source]
  have allocated : BlockContinues program env
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str"))
        (some (.list []))] base bound heap :=
    BlockContinues.annAssign (Evaluates.list .nil)
  apply (allocated
    [.forIn (.name "attempt") (.name "attempts") validationBody [], .return checkedExpression]
    anchors stack).trans
  have lookup : bound "attempts" = some value := by simpa [bound, setLocal] using getInput
  have read : Mutable.sequence value heap = some (.ok (attempts.map text), heap) := by
    simpa only [sequenceValue_source] using input.read heap (List.prefix_append _ _)
  apply Reaches.next rfl
  apply (Evaluates.lookup (module := program) lookup anchors _).trans
  exact .next (by simp [step, run, read, validationLoop, heap]) .refl

abbrev naiveArgs : List Arg := ((findFunctionIn program.body "naive").getD ([], [])).1
abbrev naiveBody : List Stmt := ((findFunctionIn program.body "naive").getD ([], [])).2

theorem naive_call_result (base : Mutable.Heap) (value : Mutable.Value)
    (attempts : List String) (input : SequenceInput base (sequenceSource value) attempts) :
    ∃ after, SourceResult (.operation (.call "naive") [value]) base
      (validatedOutcome [] attempts) after ∧ base <+: after := by
  obtain ⟨after, result, saved⟩ := naive_body_result base value attempts input
    (functionEnv naiveArgs naiveBody [value] []) rfl
  exact ⟨after, SourceResult.before _ _ _ _ _ _ (fun _ _ => .next rfl .refl) result, saved⟩

theorem naive_sequence_finishes (base : Mutable.Heap) (value : Mutable.Value)
    (attempts : List String) (input : SequenceInput base (sequenceSource value) attempts) :
    ∃ after, (call program "naive" [value] base).Finishes
      ⟨validatedOutcome [] attempts, [], after, base.length⟩ ∧ base <+: after := by
  obtain ⟨after, result, saved⟩ := naive_call_result base value attempts input
  exact ⟨after, SourceResult.finishes _ _ _ _ result base.length, saved⟩

theorem naive_list_finishes (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.list (attempts.map text))) :
    ∃ after, (call program "naive" [.ref address] base).Finishes
      ⟨validatedOutcome [] attempts, [], after, base.length⟩ ∧ base <+: after :=
  naive_sequence_finishes base (.ref address) attempts
    (SequenceInput.list base address attempts found)

theorem naive_tuple_finishes (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.tuple (attempts.map text))) :
    ∃ after, (call program "naive" [.ref address] base).Finishes
      ⟨validatedOutcome [] attempts, [], after, base.length⟩ ∧ base <+: after :=
  naive_sequence_finishes base (.ref address) attempts
    (SequenceInput.tuple base address attempts found)

end data.«project-euler-statements».data.py.project_euler_statements.p79
