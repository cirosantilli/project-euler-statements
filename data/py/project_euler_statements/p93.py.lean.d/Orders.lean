import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Filtering

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

def orderIntegers (xs : List Int) : List Int := integerResults (enumeratePairs xs)
def collectedIntegers (orders : List (List Int)) : List Int := orders.flatMap orderIntegers
def permutationSources (orders : List (List Int)) : List (List SequenceSource) :=
  orders.map (List.map (fun n => sequenceSource (Heap.number n)))

/-- A complete recursive call followed by the source's integer-filtering loop. -/
theorem order_result (xs : List Int) (base : Mutable.Heap) (old : List Int) (garbage : Mutable.Heap)
    (address : Nat) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (input : (working base (old.map Heap.number) garbage)[address]? =
      some (.tuple (xs.map Heap.number)))
    (getOrder : env "order" = some (.ref address)) (getOut : env "integers" = some (.ref base.length)) :
    ∃ extra finalEnv,
      BlockContinues program env orderBody (working base (old.map Heap.number) garbage) finalEnv
        (working base ((old ++ orderIntegers xs).map Heap.number) (garbage ++ extra)) globals ∧
      (∀ name, name ≠ "numerator" → name ≠ "denominator" → finalEnv name = env name) := by
  obtain ⟨result, extra, fresh, called, values, foundList, rows⟩ :=
    all_results.result xs (working base (old.map Heap.number) garbage) address globals input
  have different : base.length ≠ result := by
    simp only [working, List.length_append, List.length_cons] at fresh
    omega
  have foundAfter : (working base (old.map Heap.number) (garbage ++ extra))[result]? = some (.list values) := by
    simpa only [append] using foundList
  have rowsAfter : Heap.Rows (working base (old.map Heap.number) (garbage ++ extra)) values (enumeratePairs xs) := by
    simpa only [append] using rows
  obtain ⟨finalEnv, filtered, unchanged⟩ := filter_loop base result values different (enumeratePairs xs) values
    0 old (garbage ++ extra) env globals foundAfter rfl rowsAfter (enumeratePairs_spec xs).1 getOut
  refine ⟨extra, finalEnv, ?_, unchanged⟩
  apply BlockContinues.for_unpack (items := values) (value := .ref result)
    (by intro expressions; simp) rfl
    (Evaluates.call (.cons (Evaluates.lookup getOrder) .nil) called)
    (by simp [Mutable.sequence, foundList])
  simpa only [append] using filtered

/-- Each Python permutation tuple is allocated before its complete enumeration and filtering. -/
theorem orders_loop (orders : List (List Int)) (base : Mutable.Heap) (old : List Int)
    (garbage : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getOut : env "integers" = some (.ref base.length)) :
    ∃ extra finalEnv,
      BlockContinues program env [.permutationStepLoop "order" (permutationSources orders) orderBody []]
        (working base (old.map Heap.number) garbage) finalEnv
        (working base ((old ++ collectedIntegers orders).map Heap.number) (garbage ++ extra)) globals ∧
      (∀ name, name ≠ "order" → name ≠ "numerator" → name ≠ "denominator" → finalEnv name = env name) := by
  induction orders generalizing old garbage env with
  | nil =>
    refine ⟨[], env, ?_, fun _ _ _ _ => rfl⟩
    simp only [collectedIntegers, permutationSources, List.flatMap_nil, List.map_nil, List.append_nil]
    exact BlockContinues.permutation_done .nil
  | cons xs orders ih =>
    obtain ⟨address, tupleExtra, allocated, foundTuple⟩ :=
      allocate_tuple (xs.map Heap.number) (working base (old.map Heap.number) garbage)
    let bound := setLocal env "order" (.ref address)
    have getOutBound : bound "integers" = some (.ref base.length) := by
      simpa [bound, setLocal] using getOut
    obtain ⟨callExtra, after, executed, kept⟩ := order_result xs base old (garbage ++ tupleExtra) address
      bound globals (by simpa only [append] using foundTuple) (by simp [bound, setLocal]) getOutBound
    obtain ⟨later, finalEnv, continued, unchanged⟩ :=
      ih (old ++ orderIntegers xs) ((garbage ++ tupleExtra) ++ callExtra) after
        ((kept "integers" (by decide) (by decide)).trans getOutBound)
    refine ⟨tupleExtra ++ callExtra ++ later, finalEnv, ?_, ?_⟩
    · apply BlockContinues.permutation_step
        (tuple := .ref address) (middle := working base (old.map Heap.number) (garbage ++ tupleExtra))
      · simpa only [List.map_map, sequenceValue, sequenceSource, append] using allocated
      · simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, collectedIntegers, permutationSources,
          List.flatMap_cons, List.map_cons, List.append_assoc] using executed.append continued
    · intro name notOrder notN notD
      exact (unchanged name notOrder notN notD).trans
        ((kept name notN notD).trans (by simp [bound, setLocal, notOrder]))

end data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits
