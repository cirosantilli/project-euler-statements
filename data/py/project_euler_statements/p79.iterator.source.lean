import data.«project-euler-statements».data.py.project_euler_statements.«p79.validation.source»
import lang.py.FormalSW.IteratorRules
import lang.py.FormalSW.ConstructionIsolation
import lang.py.FormalSW.IteratorOperationRelocation

/-! Reference validation consumes actual iterator methods and preserves their shared effects. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

/-- The checked list may be anywhere in the heap, with later iterator allocations after it. -/
theorem accepted_attempt_at (heap : Mutable.Heap) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (s : String)
    (found : heap[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (getAttempt : env "attempt" = some (text s))
    (length : s.length = 3) (digits : Strings.isDigit s = true) :
    BlockContinues program env validationBody heap env
      (heap.set address (.list ((checked ++ [s]).map text))) := by
  apply (valid_guard env heap s getAttempt length digits).append
  apply BlockContinues.discard
  have appended := Evaluates.append (module := program) (globals := [])
    (value := text s) (current := checked.map text)
    (Evaluates.lookup (name := "checked") getChecked) found
    (Evaluates.lookup (name := "attempt") getAttempt) found
  simpa [List.map_append] using appended

abbrev validationIteratorLoop (env : HeapCalls.Env) (following : List Stmt)
    (stack : List HeapCalls.Frame) : IteratorCalls.Loop :=
  ⟨"attempt", validationBody, [], following, env, stack⟩

theorem iterator_accepted_attempt (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) := by
  have body := accepted_attempt_at yielded address checked (setLocal env "attempt" (text s)) s
    found (by simpa [setLocal] using getChecked) (by simp [setLocal]) length digits
  exact IteratorCalls.advance_continue (loop := validationIteratorLoop env following stack)
    isObject bound executed rfl (body.extend extension)

/-- The only reference-body write is to its private checked list. -/
theorem iterator_accepted_preserves (heap : Mutable.Heap) (address observed : Nat)
    (checked : List String) (s : String) (separate : address ≠ observed) :
    (heap.set address (.list ((checked ++ [s]).map text)))[observed]? = heap[observed]? := by
  simp [separate]

/-- Reference validation cannot alter the empty-tuple identity seen by the iterator. -/
theorem iterator_accepted_emptyTuple (heap : Mutable.Heap) (address : Nat)
    (checked : List String) (s : String)
    (found : heap[address]? = some (.list (checked.map text))) :
    Mutable.Relocation.emptyTupleAddress
      (heap.set address (.list ((checked ++ [s]).map text))) =
      Mutable.Relocation.emptyTupleAddress heap :=
  Mutable.Relocation.emptyTupleAddress_set _ _ _ _ found (by simp) (by simp)

/-- Appending a validated string preserves every relocated caller object. -/
theorem iterator_accepted_layout (logical heap : Mutable.Heap) (rename : Nat → Nat)
    (address : Nat) (checked : List String) (s : String)
    (layout : Mutable.Relocation.HeapLayout logical heap rename)
    (separate : ∀ index < logical.length, address ≠ rename index) :
    Mutable.Relocation.HeapLayout logical
      (heap.set address (.list ((checked ++ [s]).map text))) rename := by
  apply layout.preserves
  intro index inside
  exact iterator_accepted_preserves heap address (rename index) checked s (separate index inside)

/-- Actual iterator execution followed by validation preserves its relocated caller graph. -/
theorem iterator_accepted_attempt_layout (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (logical : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.HeapLayout logical yielded rename)
    (separate : ∀ index < logical.length, address ≠ rename index)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.HeapLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename ∧
      Mutable.Relocation.emptyTupleAddress
        (yielded.set address (.list ((checked ++ [s]).map text))) =
        Mutable.Relocation.emptyTupleAddress yielded := by
  obtain ⟨finalUsed, run⟩ := iterator_accepted_attempt context extension choices anchors used
    before yielded iterator operation address checked env s length digits isObject bound executed
    found getChecked following stack resumes
  exact ⟨finalUsed, run, iterator_accepted_layout logical yielded rename address checked s
    layout separate, iterator_accepted_emptyTuple yielded address checked s found⟩

/-- Appending a validated string retains the exact runtime objects used by the iterator. -/
theorem iterator_accepted_runtime (logical heap : Mutable.Heap) (rename : Nat → Nat)
    (address : Nat) (checked : List String) (s : String)
    (layout : Mutable.Relocation.RuntimeLayout logical heap rename)
    (separate : ∀ index < logical.length, address ≠ rename index) :
    Mutable.Relocation.RuntimeLayout logical
      (heap.set address (.list ((checked ++ [s]).map text))) rename := by
  apply layout.preserves
  intro index inside
  exact iterator_accepted_preserves heap address (rename index) checked s (separate index inside)

/-- Actual iterator execution followed by validation retains the complete runtime layout. -/
theorem iterator_accepted_attempt_runtime (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (logical : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.RuntimeLayout logical yielded rename)
    (separate : ∀ index < logical.length, address ≠ rename index)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.RuntimeLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename ∧
      Mutable.Relocation.emptyTupleAddress
        (yielded.set address (.list ((checked ++ [s]).map text))) =
        Mutable.Relocation.emptyTupleAddress yielded := by
  obtain ⟨finalUsed, run⟩ := iterator_accepted_attempt context extension choices anchors used
    before yielded iterator operation address checked env s length digits isObject bound executed
    found getChecked following stack resumes
  exact ⟨finalUsed, run, iterator_accepted_runtime logical yielded rename address checked s
    layout separate, iterator_accepted_emptyTuple yielded address checked s found⟩

/-- Reference validation preserves the invariants needed to execute the next iterator method. -/
theorem iterator_accepted_attempt_execution (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (address : Nat) (checked : List String) (env : HeapCalls.Env)
    (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (found : yielded[address]? = some (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (logical : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.ExecutionLayout logical yielded rename)
    (separate : ∀ index < logical.length, address ≠ rename index)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.ExecutionLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename ∧
      Mutable.Relocation.emptyTupleAddress
        (yielded.set address (.list ((checked ++ [s]).map text))) =
        Mutable.Relocation.emptyTupleAddress yielded := by
  obtain ⟨finalUsed, run, related, interned⟩ := iterator_accepted_attempt_runtime
    context extension choices anchors used before yielded iterator operation address checked env s
    length digits isObject bound executed found getChecked logical rename layout.runtime separate
    following stack resumes
  exact ⟨finalUsed, run, layout.preserves related interned, interned⟩

/-- Validation updates the protected list and retains separation for the next caller method. -/
theorem iterator_accepted_attempt_private (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded logical : Mutable.Heap)
    (rename : Nat → Nat) (iterator : Mutable.Value) (operation : Operation)
    (address : Nat) (checked : List String) (env : HeapCalls.Env) (s : String)
    (length : s.length = 3) (digits : Strings.isDigit s = true)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before = some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation before (.ok (text s)) yielded)
    (protectedLayout : Mutable.Relocation.PrivateLayout logical yielded rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env, stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following)
        (setLocal env "attempt" (text s)), stack,
        yielded.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      Mutable.Relocation.PrivateLayout logical
        (yielded.set address (.list ((checked ++ [s]).map text))) rename address (.list ((checked ++ [s]).map text)) := by
  obtain ⟨finalUsed, run⟩ := iterator_accepted_attempt context extension choices anchors used before yielded
    iterator operation address checked env s length digits isObject bound executed protectedLayout.saved getChecked following stack resumes
  exact ⟨finalUsed, run, protectedLayout.update_private _ (by simp) (by simp)⟩

theorem iterator_rejected_attempt (context : Module) (extension : Extends context program)
    (choices : ChoiceSchedule) (anchors used : Nat) (before yielded : Mutable.Heap)
    (iterator : Mutable.Value)
    (operation : Operation) (env : HeapCalls.Env) (s : String)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok (text s)) yielded)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.completed (.ok ⟨.error (invalidException s), [], yielded, anchors⟩) finalUsed resumes) := by
  obtain ⟨middleUsed, advanced⟩ := IteratorCalls.advance_returns
    (loop := validationIteratorLoop env following stack) (anchors := anchors) (used := used)
    (resumes := resumes) isObject bound executed
  have rejected := rejected_attempt (setLocal env "attempt" (text s)) yielded s
    (by simp [setLocal]) invalid (validationLoop (sequenceSource iterator) 0 :: following)
      anchors stack
  obtain ⟨finalUsed, failed⟩ := IteratorCalls.completion_of_set
    (SetCalls.finishes_of_heap (finishes_extend rejected extension) choices middleUsed)
    (by intro completion same; cases same; simp [invalidException]) resumes
  refine ⟨finalUsed, advanced.trans ?_⟩
  simpa only [IteratorCalls.loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using failed


/-- The source for statement evaluates and acquires its input exactly once. -/
theorem iterator_enter (context : Module) (choices : ChoiceSchedule) (anchors used : Nat)
    (before after : Mutable.Heap) (receiver iterator : Mutable.Value)
    (operation advance : Operation) (env : HeapCalls.Env)
    (getInput : env "attempts" = some receiver)
    (isObject : IteratorCalls.isInstance before receiver = true)
    (bound : ProtocolCalls.iterMethod context receiver before = some (.ok operation, before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.ok iterator) after)
    (valid : ProtocolCalls.nextMethod context iterator after = some (.ok (some advance), after))
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (.forIn (.name "attempt") (.name "attempts") validationBody [] ::
        following) env, stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, after⟩, finalUsed⟩ resumes) :=
  IteratorCalls.for_instance (loop := validationIteratorLoop env following stack)
    (by intro expressions impossible; cases impossible)
    (Evaluates.lookup getInput) isObject bound executed valid

/-- Non-exhaustion failures escape before validation or updates to the graph or checked list. -/
theorem iterator_failed (context : Module) (choices : ChoiceSchedule) (anchors used : Nat)
    (before after : Mutable.Heap) (iterator : Mutable.Value) (operation : Operation)
    (env : HeapCalls.Env) (error : ExceptionObject)
    (notExhausted : error.typeName ≠ "StopIteration")
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation
      before (.error error) after)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.completed (.ok ⟨.error error, [], after, anchors⟩) finalUsed resumes) :=
  IteratorCalls.advance_failed (loop := validationIteratorLoop env following stack)
    isObject bound executed notExhausted

theorem iterator_exhausted (context : Module) (choices : ChoiceSchedule) (anchors used : Nat)
    (before after : Mutable.Heap) (iterator : Mutable.Value) (operation : Operation)
    (env : HeapCalls.Env) (args : List Constant)
    (isObject : IteratorCalls.isInstance before iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator before =
      some (.ok (some operation), before))
    (executed : IteratorCalls.OperationCompletes context choices used operation before
      (.error ⟨"StopIteration", args⟩) after)
    (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ finalUsed, IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: following) env,
        stack, before⟩, used⟩ resumes)
      (.running ⟨⟨.block following env, stack, after⟩, finalUsed⟩ resumes) :=
  IteratorCalls.advance_exhausted (loop := validationIteratorLoop env following stack)
    isObject bound executed

/-- One logical advancement supplies the reference consumer's actual call and yielded string. -/
theorem iterator_next_relocated (context : Module)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (anchors used : Nat) (logical physical after : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.ExecutionLayout logical physical rename)
    (iterator : Mutable.Value) (inside : iterator.edge.Within logical.length) (operation : Operation)
    (isObject : IteratorCalls.isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator logical = some (.ok (some operation), logical))
    (s : String) (executed : IteratorCalls.OperationCompletes context choices used operation logical (.ok (text s)) after)
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ other nextMap finalUsed,
      IteratorCalls.Relocation.ExtendedLayout logical.length physical.length rename after other nextMap ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
          stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationBody ++
          [Calls.loopContinuation validationBody
            (validationLoop (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0)] ++ following)
          (setLocal env "attempt" (text s)), stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, logicalRun⟩ := executed logical.length []
  obtain ⟨other, nextMap, extended, called⟩ := IteratorCalls.Relocation.advance_completion_relocates context choices
    logical physical rename logical.length anchors used finalUsed iterator operation (.ok (text s)) after []
    source layout inside (by simp [HeapCalls.Relocation.GlobalsWithin]) isObject bound logicalRun
  refine ⟨other, nextMap, finalUsed, extended, ?_⟩
  have calledRun := called (validationIteratorLoop env following stack) resumes
  have completion : IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop
        (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
        stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.ok (text s), [], other, anchors⟩) finalUsed
        (.advance (validationIteratorLoop env following stack) (Mutable.Relocation.relocateValue rename iterator) :: resumes)) := by
    simpa only [HeapCalls.Relocation.relocateGlobals, List.map_nil, Except.map,
      text, Mutable.Relocation.relocateValue] using calledRun
  exact IteratorCalls.advanced completion

/-- Exhaustion transports its final mutations before the reference loop exits. -/
theorem iterator_exhausted_relocated (context : Module)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (anchors used : Nat) (logical physical after : Mutable.Heap) (rename : Nat → Nat)
    (layout : Mutable.Relocation.ExecutionLayout logical physical rename)
    (iterator : Mutable.Value) (inside : iterator.edge.Within logical.length) (operation : Operation)
    (isObject : IteratorCalls.isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator logical = some (.ok (some operation), logical))
    (args : List Constant) (executed : IteratorCalls.OperationCompletes context choices used operation logical
      (.error ⟨"StopIteration", args⟩) after)
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame)
    (resumes : List IteratorCalls.Resume) :
    ∃ other nextMap finalUsed,
      IteratorCalls.Relocation.ExtendedLayout logical.length physical.length rename after other nextMap ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
          stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block following env, stack, other⟩, finalUsed⟩ resumes) := by
  obtain ⟨finalUsed, logicalRun⟩ := executed logical.length []
  obtain ⟨other, nextMap, extended, called⟩ := IteratorCalls.Relocation.advance_completion_relocates context choices
    logical physical rename logical.length anchors used finalUsed iterator operation (.error ⟨"StopIteration", args⟩) after []
    source layout inside (by simp [HeapCalls.Relocation.GlobalsWithin]) isObject bound logicalRun
  refine ⟨other, nextMap, finalUsed, extended, ?_⟩
  have completion : IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop
        (sequenceSource (Mutable.Relocation.relocateValue rename iterator)) 0 :: following) env,
        stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.error ⟨"StopIteration", args⟩, [], other, anchors⟩) finalUsed
        (.advance (validationIteratorLoop env following stack) (Mutable.Relocation.relocateValue rename iterator) :: resumes)) := by
    simpa only [HeapCalls.Relocation.relocateGlobals, List.map_nil, Except.map] using
      called (validationIteratorLoop env following stack) resumes
  exact IteratorCalls.exhausted completion

end data.«project-euler-statements».data.py.project_euler_statements.p79
