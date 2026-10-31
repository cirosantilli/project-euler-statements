import data.«project-euler-statements».data.py.project_euler_statements.«p79.dedup.source»

/-! The nested reference comprehension visits Unicode characters and builds distinct graph nodes. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def attemptCharacters (attempts : List String) : List String :=
  attempts.flatMap (fun s => s.toList.map String.singleton)

def nodeValues (attempts : List String) : List String := dedupBy id [] (attemptCharacters attempts)

def collectNodes : Expr :=
  .listComp (.name "c") [("s", .name "attempts", []), ("c", .name "s", [])]

def collectCharacters (collector : Nat) : List Stmt :=
  [.forIn (.name "c") (.name "s") [.comprehensionAppend collector (.name "c")] []]

theorem nodes_source : executableBody
    ((findFunctionIn program.body "nodes").getD ([], [])).2 =
      [.return (.call (.name "erase_dups") [collectNodes])] := rfl

theorem collect_characters_loop (base : Mutable.Heap) (s : String)
    (before remaining : List Char) (collected : List String)
    (partition : s.toList = before ++ remaining) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "c" (.scalar (.string s)) before.length
        [.comprehensionAppend base.length (.name "c")] []]
      (base ++ [.list (collected.map text)]) finalEnv
      (base ++ [.list ((collected ++ remaining.map String.singleton).map text)]) := by
  induction remaining generalizing before collected env with
  | nil =>
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done
        (items := s.toList.map (fun c => text (String.singleton c)))
        (by simp [sequenceValue, Mutable.sequence])
      · simp [partition]
      · simpa using (BlockContinues.nil (module := program) (env := env)
          (heap := base ++ [.list (collected.map text)]))
  | cons c rest ih =>
      let bound := setLocal env "c" (text (String.singleton c))
      have emitted := BlockContinues.comprehension_append (module := program) (globals := [])
        (env := bound) (expression := .name "c") (address := base.length)
        (items := collected.map text) (heap := base ++ [.list (collected.map text)])
        (Evaluates.lookup (value := text (String.singleton c)) (by simp [bound, setLocal]))
        (by simp)
      obtain ⟨finalEnv, continued⟩ := ih (before ++ [c]) (collected ++ [String.singleton c])
        (by simpa [List.append_assoc] using partition) bound
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step
        (items := s.toList.map (fun c => text (String.singleton c)))
        (value := text (String.singleton c))
        (by simp [sequenceValue, Mutable.sequence]) (by simp [partition])
      have emitted' : BlockContinues program bound
          [.comprehensionAppend base.length (.name "c")]
          (base ++ [.list (collected.map text)]) bound
          (base ++ [.list ((collected ++ [String.singleton c]).map text)]) := by
        simpa [List.map_append] using emitted
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.append_assoc, bound] using emitted'.append continued

theorem collect_nodes_loop (base : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : base[address]? = some (.list (attempts.map text)))
    (before remaining collected : List String) (partition : attempts = before ++ remaining)
    (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "s" (.ref address) before.length (collectCharacters base.length) []]
      (base ++ [.list (collected.map text)]) finalEnv
      (base ++ [.list ((collected ++ attemptCharacters remaining).map text)]) := by
  have input (values : List String) : (base ++ [.list (values.map text)])[address]? =
      some (.list (attempts.map text)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  induction remaining generalizing before collected env with
  | nil =>
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done (items := attempts.map text)
        (by simp [sequenceValue, Mutable.sequence, input])
      · simp [partition]
      · simpa [attemptCharacters] using (BlockContinues.nil (module := program) (env := env)
          (heap := base ++ [.list (collected.map text)]))
  | cons s rest ih =>
      let bound := setLocal env "s" (text s)
      obtain ⟨innerEnv, inner⟩ := collect_characters_loop base s [] s.toList collected rfl bound
      have collectedStep : BlockContinues program bound (collectCharacters base.length)
          (base ++ [.list (collected.map text)]) innerEnv
          (base ++ [.list ((collected ++ s.toList.map String.singleton).map text)]) := by
        apply BlockContinues.for_sequence (value := text s)
          (items := s.toList.map (fun c => text (String.singleton c)))
          (by intros; intro impossible; cases impossible)
          (Evaluates.lookup (by simp [bound, setLocal]))
          (by simp [Mutable.sequence])
        exact inner
      obtain ⟨finalEnv, continued⟩ := ih (before ++ [s])
        (collected ++ s.toList.map String.singleton)
        (by simpa [List.append_assoc] using partition) innerEnv
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (items := attempts.map text) (value := text s)
        (by simp [sequenceValue, Mutable.sequence, input]) (by simp [partition])
      simpa [collectCharacters, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        attemptCharacters, List.append_assoc, bound] using collectedStep.append continued

theorem collect_nodes_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getAttempts : env "attempts" = some (.ref address)) :
    Evaluates program env collectNodes heap (.ref heap.length)
      (heap ++ [.list ((attemptCharacters attempts).map text)]) := by
  obtain ⟨finalEnv, collected⟩ := collect_nodes_loop heap address attempts found [] attempts [] rfl
    (comprehensionEnv env [("s", .name "attempts", []), ("c", .name "s", [])])
  apply Evaluates.list_comp_sequence (items := attempts.map text)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getAttempts)
    (by simp [Mutable.sequence, found])
  simpa only [List.length_nil, List.nil_append] using collected

theorem nodes_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text))) :
    ReturnsValue program "nodes" [.ref address] heap (.ref (heap.length + 1))
      (heap ++ [.list ((attemptCharacters attempts).map text),
        .list ((nodeValues attempts).map text)]) := by
  let source := (findFunctionIn program.body "nodes").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref address] []
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have called := Evaluates.call
    (.cons (collect_nodes_result heap address attempts found env rfl) .nil)
    (dedup_strings (heap ++ [.list ((attemptCharacters attempts).map text)]) heap.length
      (attemptCharacters attempts) (by simp))
  simpa [nodeValues, List.append_assoc] using called

theorem node_values_unique (attempts : List String) : (nodeValues attempts).Nodup := by
  simpa [nodeValues] using dedupBy_unique id [] (attemptCharacters attempts) (by simp)

theorem node_values_mem (attempts : List String) (value : String) :
    value ∈ nodeValues attempts ↔
      ∃ s ∈ attempts, ∃ c ∈ s.toList, String.singleton c = value := by
  simpa [nodeValues, attemptCharacters] using
    dedupBy_keys id [] (attemptCharacters attempts) value

end data.«project-euler-statements».data.py.project_euler_statements.p79
