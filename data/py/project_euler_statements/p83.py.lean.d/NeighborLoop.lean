import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».NeighborCandidates

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.TriangleBufferCalls (number)
set_option Elab.async false

abbrev PairRows := List (Nat × (Int × Int))
abbrev insideGrid (height width : Nat) (pair : Int × Int) : Bool :=
  decide (0 ≤ pair.1 ∧ 0 ≤ pair.2 ∧ pair.1 < height ∧ pair.2 < width)
def pairRefs (base : Mutable.Heap) (count : Nat) : List Mutable.Value :=
  (List.range count).map (fun index => .ref (base.length + 1 + index))
def pairHeap (base : Mutable.Heap) (output : List (Int × Int)) : Mutable.Heap :=
  base ++ [.list (pairRefs base output.length)] ++ output.map (fun pair => .tuple (pairFields pair))
abbrev neighborTarget : Expr := .tuple [.name "rr", .name "cc"]
abbrev neighborBody (address : Nat) : List Stmt :=
  [.assign [neighborTarget] (.name "$formalsw.unpack"),
   .ifThen neighborFilter [.comprehensionAppend address neighborTarget] []]

theorem pair_heap_read (base : Mutable.Heap) (output : List (Int × Int)) (address : Nat) (object : Mutable.Object)
    (found : base[address]? = some object) : (pairHeap base output)[address]? = some object := by
  unfold pairHeap
  rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem pair_heap_append (base : Mutable.Heap) (output : List (Int × Int)) (pair : Int × Int) :
    ((pairHeap base output) ++ [Mutable.Object.tuple (pairFields pair)]).set base.length
      (Mutable.Object.list (pairRefs base output.length ++ [Mutable.Value.ref (pairHeap base output).length])) = pairHeap base (output ++ [pair]) := by
  simp [pairHeap, pairRefs, List.range_succ, List.append_assoc]; omega

theorem neighbor_loop (base : Mutable.Heap) (env : HeapCalls.Env) (address position height width : Nat)
    (rows : PairRows) (output : List (Int × Int))
    (found : base[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, base[pair.1]? = some (.tuple (pairFields pair.2)))
    (localHeight : env "rows" = some (number height)) (localWidth : env "cols" = some (number width)) :
    ∃ after, BlockContinues program env
      [.sequenceStepLoop "$formalsw.unpack" (.ref address) position (neighborBody base.length) []]
      (pairHeap base output) after
      (pairHeap base (output ++ ((rows.drop position).map Prod.snd).filter (insideGrid height width))) := by
  let state := pairHeap base output
  have source : Mutable.sequence (.ref address) state =
      some (.ok (rows.map (fun pair => .ref pair.1)), state) := by
    simp [state, Mutable.sequence, pair_heap_read base output address _ found]
  by_cases active : position < rows.length
  · let pair := rows[position]
    let fetched := setLocal env "$formalsw.unpack" (.ref pair.1)
    let entered := assignNames fetched ["rr", "cc"] (pairFields pair.2)
    have item : (rows.map (fun pair => Mutable.Value.ref pair.1))[position]? = some (.ref pair.1) := by
      simp [List.getElem?_eq_getElem active, pair]
    have fields : Mutable.sequence (.ref pair.1) state = some (.ok (pairFields pair.2), state) := by
      simp [Mutable.sequence, state, pair_heap_read base output pair.1 _ (reads pair (List.getElem_mem active))]
    have unpacked : BlockContinues program fetched [.assign [neighborTarget] (.name "$formalsw.unpack")]
        state entered state := BlockContinues.unpack rfl (Evaluates.lookup rfl) fields rfl
    have tested := neighbor_filter state entered pair.2.1 pair.2.2 height width rfl rfl
      (by simpa [entered, fetched, assignNames, setLocal] using localHeight)
      (by simpa [entered, fetched, assignNames, setLocal] using localWidth)
    by_cases accepted : insideGrid height width pair.2 = true
    · have tuple : Evaluates program entered neighborTarget state (.ref state.length)
          (state ++ [.tuple (pairFields pair.2)]) :=
        Evaluates.tuple (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) (by simp)
      have collector : (state ++ [.tuple (pairFields pair.2)])[base.length]? = some (.list (pairRefs base output.length)) := by
        simp [state, pairHeap, List.append_assoc]
      have emitted := BlockContinues.comprehension_append tuple collector
      rw [pair_heap_append] at emitted
      have branch : BlockContinues program entered [.ifThen neighborFilter [.comprehensionAppend base.length neighborTarget] []]
          state entered (pairHeap base (output ++ [pair.2])) :=
        BlockContinues.branch (flag := true) (by simpa only [accepted] using tested) rfl emitted
      obtain ⟨after, continued⟩ := neighbor_loop base entered address (position + 1) height width rows (output ++ [pair.2]) found reads
        (by simpa [entered, fetched, assignNames, setLocal] using localHeight)
        (by simpa [entered, fetched, assignNames, setLocal] using localWidth)
      refine ⟨after, ?_⟩
      apply BlockContinues.sequence_step (source := .ref address) source item
      simpa only [neighborBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.drop_eq_getElem_cons active, List.map_cons,
        List.filter_cons, accepted, if_true, pair, List.append_assoc, List.singleton_append] using
        (unpacked.append branch).append continued
    · have rejected : insideGrid height width pair.2 = false := Bool.eq_false_iff.mpr accepted
      have branch : BlockContinues program entered [.ifThen neighborFilter [.comprehensionAppend base.length neighborTarget] []]
          state entered state :=
        BlockContinues.branch (flag := false) (by simpa only [rejected] using tested) rfl BlockContinues.nil
      obtain ⟨after, continued⟩ := neighbor_loop base entered address (position + 1) height width rows output found reads
        (by simpa [entered, fetched, assignNames, setLocal] using localHeight)
        (by simpa [entered, fetched, assignNames, setLocal] using localWidth)
      refine ⟨after, ?_⟩
      apply BlockContinues.sequence_step (source := .ref address) source item
      simpa only [neighborBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.drop_eq_getElem_cons active, List.map_cons,
        List.filter_cons, rejected, pair] using (unpacked.append branch).append continued
  · have gone : rows.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨env, ?_⟩
    simp only [gone, List.map_nil, List.filter_nil, List.append_nil]
    exact BlockContinues.sequence_done (source := .ref address) source
      (by simp [List.getElem?_eq_none (by omega : rows.length ≤ position)]) BlockContinues.nil
termination_by rows.length - position
decreasing_by all_goals omega

end data.«project-euler-statements».data.py.project_euler_statements.p83
