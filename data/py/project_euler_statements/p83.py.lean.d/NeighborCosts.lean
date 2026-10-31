import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Neighbors
import ProjectEulerSolutions.Lib.TriangleBufferCalls
import ProjectEulerSolutions.Lib.RectangularMatrixCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls
open ProjectEulerStatements.P83 (getD2 neighbors)
set_option Elab.async false

abbrev neighborCost : Expr := .call (.name "get_d2") [.name "dist", .name "rr", .name "cc"]
abbrev neighborCall : Expr := .call (.name "neighbors") [.name "r", .name "c", .name "rows", .name "cols"]
abbrev neighborCostsExpression : Expr := .listCompTargets neighborCost [(neighborTarget, neighborCall, [])]
abbrev neighborCostBody (address : Nat) : List Stmt :=
  [.assign [neighborTarget] (.name "$formalsw.unpack"), .comprehensionAppend address neighborCost]

theorem neighbor_cost_loop (base : Mutable.Heap) (env : HeapCalls.Env)
    (address position distanceAddress : Nat) (pairs : PairRows) (matrix : MatrixRows) (output : List Int)
    (found : base[address]? = some (.list (pairs.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ pairs, base[pair.1]? = some (.tuple (pairFields pair.2)))
    (distanceFound : base[distanceAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ matrix, base[row.1]? = some (.list (encode row.2)))
    (localDistances : env "dist" = some (.ref distanceAddress)) :
    ∃ after, BlockContinues program env
      [.sequenceStepLoop "$formalsw.unpack" (.ref address) position (neighborCostBody base.length) []]
      (working base output) after
      (working base (output ++ (pairs.drop position).map (fun pair => getD2 (matrix.map Prod.snd) pair.2.1 pair.2.2))) := by
  let state := working base output
  have source : Mutable.sequence (.ref address) state = some (.ok (pairs.map (fun pair => .ref pair.1)), state) := by
    simp [state, Mutable.sequence, prefix_found base output address _ found]
  by_cases active : position < pairs.length
  · let pair := pairs[position]
    let fetched := setLocal env "$formalsw.unpack" (.ref pair.1)
    let entered := assignNames fetched ["rr", "cc"] (pairFields pair.2)
    have item : (pairs.map (fun pair => Mutable.Value.ref pair.1))[position]? = some (.ref pair.1) := by
      simp [List.getElem?_eq_getElem active, pair]
    have fields : Mutable.sequence (.ref pair.1) state = some (.ok (pairFields pair.2), state) := by
      simp [Mutable.sequence, state, prefix_found base output pair.1 _ (reads pair (List.getElem_mem active))]
    have unpacked : BlockContinues program fetched [.assign [neighborTarget] (.name "$formalsw.unpack")] state entered state :=
      BlockContinues.unpack rfl (Evaluates.lookup rfl) fields rfl
    have element : Evaluates program entered neighborCost state
        (number (getD2 (matrix.map Prod.snd) pair.2.1 pair.2.2)) state :=
      Evaluates.call
        (.cons (Evaluates.lookup (by simpa [entered, fetched, assignNames, setLocal] using localDistances))
          (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)))
        (get_d2.result state distanceAddress matrix pair.2.1 pair.2.2
          (prefix_found base output distanceAddress _ distanceFound)
          (fun row member => prefix_found base output row.1 _ (distanceReads row member)))
    have emitted := BlockContinues.comprehension_append element (ProjectEulerSolutions.TriangleBufferCalls.found base output)
    have write : state.set base.length (.list (encode output ++ [number (getD2 (matrix.map Prod.snd) pair.2.1 pair.2.2)])) =
        working base (output ++ [getD2 (matrix.map Prod.snd) pair.2.1 pair.2.2]) := by simp [state, working, encode]
    rw [write] at emitted
    obtain ⟨after, continued⟩ := neighbor_cost_loop base entered address (position + 1) distanceAddress pairs matrix
      (output ++ [getD2 (matrix.map Prod.snd) pair.2.1 pair.2.2]) found reads distanceFound distanceReads
      (by simpa [entered, fetched, assignNames, setLocal] using localDistances)
    refine ⟨after, ?_⟩
    apply BlockContinues.sequence_step (source := .ref address) source item
    simpa only [neighborCostBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
      Bool.false_or, Bool.false_eq_true, if_false, List.drop_eq_getElem_cons active, List.map_cons,
      pair, List.append_assoc, List.singleton_append] using (unpacked.append emitted).append continued
  · have gone : pairs.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨env, ?_⟩
    simp only [gone, List.map_nil, List.append_nil]
    exact BlockContinues.sequence_done (source := .ref address) source
      (by simp [List.getElem?_eq_none (by omega : pairs.length ≤ position)]) BlockContinues.nil
termination_by pairs.length - position
decreasing_by omega

theorem neighbor_costs_allocation (heap : Mutable.Heap) (env : HeapCalls.Env)
    (distanceAddress height width : Nat) (matrix : MatrixRows) (r c : Int)
    (distanceFound : heap[distanceAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2)))
    (localDistances : env "dist" = some (.ref distanceAddress)) (localRow : env "r" = some (number r))
    (localCol : env "c" = some (number c)) (localHeight : env "rows" = some (number height))
    (localWidth : env "cols" = some (number width)) :
    ∃ (extra : Mutable.Heap) (address : Nat),
      Evaluates program env neighborCostsExpression heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (encode ((neighbors r c height width).map
        (fun pair => getD2 (matrix.map Prod.snd) pair.1 pair.2)))) := by
  obtain ⟨allocated, sourceAddress, pairs, returned, found, reads, values⟩ := neighbors.complete heap r c height width
  let base := heap ++ allocated
  let scopedEnv := comprehensionTargetsEnv env [(neighborTarget, neighborCall, [])]
  have kept (target : Nat) (object : Mutable.Object) (read : heap[target]? = some object) : base[target]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
    exact read
  obtain ⟨after, loop⟩ := neighbor_cost_loop base scopedEnv sourceAddress 0 distanceAddress pairs matrix [] found reads
    (kept _ _ distanceFound) (fun row member => kept _ _ (distanceReads row member))
    (by simpa [scopedEnv, comprehensionTargetsEnv, neighborTarget, targetLocals] using localDistances)
  have mapped : pairs.map (fun pair => getD2 (matrix.map Prod.snd) pair.2.1 pair.2.2) =
      (neighbors r c height width).map (fun pair => getD2 (matrix.map Prod.snd) pair.1 pair.2) := by
    rw [← values, List.map_map]
    rfl
  let costs := (neighbors r c height width).map (fun pair => getD2 (matrix.map Prod.snd) pair.1 pair.2)
  have evaluated : Evaluates program env neighborCostsExpression heap (.ref base.length) (working base costs) := by
    apply Evaluates.list_comp_targets_sequence
      (by intro expressions; simp) (by intro expressions; simp)
      (by intros expressions impossible; cases impossible)
      (Evaluates.call (.cons (Evaluates.lookup localRow) (.cons (Evaluates.lookup localCol)
        (.cons (Evaluates.lookup localHeight) (.cons (Evaluates.lookup localWidth) .nil)))) returned)
      (items := pairs.map (fun pair => .ref pair.1)) (by simp [Mutable.sequence, found])
    simpa only [working, encode, List.map_nil, List.drop_zero, List.nil_append, mapped, neighborCostBody,
      comprehensionTargetName, comprehensionTargetBody, comprehensionFilters, comprehensionTargetsBody] using loop
  refine ⟨allocated ++ [.list (encode costs)], base.length, ?_, ?_⟩
  · simpa only [working, base, List.append_assoc] using evaluated
  · simpa only [working, base, List.append_assoc] using ProjectEulerSolutions.TriangleBufferCalls.found base costs

end data.«project-euler-statements».data.py.project_euler_statements.p83
