import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».NeighborLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.TriangleBufferCalls (number)
open ProjectEulerStatements.P83 (neighbors)
set_option Elab.async false

def pairRecords (base : Mutable.Heap) (output : List (Int × Int)) : PairRows :=
  output.zipIdx.map (fun item => (base.length + 1 + item.2, item.1))

theorem pair_records_values (base : Mutable.Heap) (output : List (Int × Int)) :
    (pairRecords base output).map Prod.snd = output := by
  simp only [pairRecords, List.map_map, Function.comp_def]
  exact List.zipIdx_map_fst 0 output

theorem pair_records_refs (base : Mutable.Heap) (output : List (Int × Int)) :
    (pairRecords base output).map (fun pair => Mutable.Value.ref pair.1) = pairRefs base output.length := by
  calc
    _ = (output.zipIdx.map Prod.snd).map (fun index => Mutable.Value.ref (base.length + 1 + index)) := by
      simp only [pairRecords, List.map_map, Function.comp_def]
    _ = _ := by rw [List.zipIdx_map_snd]; rw [pairRefs, List.range_eq_range']

theorem pair_records_found (base : Mutable.Heap) (output : List (Int × Int)) :
    (pairHeap base output)[base.length]? = some (.list ((pairRecords base output).map (fun pair => .ref pair.1))) := by
  rw [pair_records_refs]
  simp [pairHeap, List.append_assoc]

theorem pair_records_read (base : Mutable.Heap) (output : List (Int × Int)) :
    ∀ pair ∈ pairRecords base output, (pairHeap base output)[pair.1]? = some (.tuple (pairFields pair.2)) := by
  intro pair member
  obtain ⟨⟨point, index⟩, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨_, inside, same⟩ := List.mem_zipIdx present
  have bound : index < output.length := by omega
  have equal : point = output[index] := by simpa using same
  unfold pairHeap
  rw [List.getElem?_append_right (by simp)]
  simp [List.getElem?_eq_getElem bound, equal]

abbrev neighborArgs : List Arg :=
  [⟨"r", some (.name "int"), none⟩, ⟨"c", some (.name "int"), none⟩,
   ⟨"rows", some (.name "int"), none⟩, ⟨"cols", some (.name "int"), none⟩]
abbrev neighborExpression : Expr := .listCompTargets neighborTarget
  [(neighborTarget, .list candidateExpressions, [neighborFilter])]
def candidateRecords (heap : Mutable.Heap) (r c : Int) : PairRows :=
  [(heap.length, (r + 1, c)), (heap.length + 1, (r, c + 1)),
   (heap.length + 2, (r, c - 1)), (heap.length + 3, (r - 1, c))]

theorem neighbors.result (heap : Mutable.Heap) (r c : Int) (height width : Nat) :
    ReturnsValue program "neighbors" [number r, number c, number height, number width] heap
      (.ref (heap.length + 5)) (pairHeap (candidateHeap heap r c) (neighbors r c height width)) := by
  let entry := argumentEnv neighborArgs [number r, number c, number height, number width]
  let base := candidateHeap heap r c
  let records := candidateRecords heap r c
  let scopedEnv := comprehensionTargetsEnv entry [(neighborTarget, .list candidateExpressions, [neighborFilter])]
  have source : base[heap.length + 4]? = some (.list (records.map (fun pair => .ref pair.1))) := by
    simp [base, candidateHeap, records, candidateRecords, candidateRefs, List.append_assoc]
  have reads : ∀ pair ∈ records, base[pair.1]? = some (.tuple (pairFields pair.2)) := by
    intro pair member
    simp only [records, candidateRecords, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [base, candidateHeap, List.append_assoc]
  obtain ⟨after, loop⟩ := neighbor_loop base scopedEnv (heap.length + 4) 0 height width records [] source reads
    (by simp [scopedEnv, comprehensionTargetsEnv, neighborTarget, targetLocals]; rfl)
    (by simp [scopedEnv, comprehensionTargetsEnv, neighborTarget, targetLocals]; rfl)
  have listEval := candidate_allocation heap entry r c rfl rfl
  have comprehension : Evaluates program entry neighborExpression heap (.ref base.length)
      (pairHeap base (neighbors r c height width)) := by
    apply Evaluates.list_comp_targets_sequence
      (by intros expressions impossible; cases impossible) (by intros expressions impossible; cases impossible)
      (by intros expressions impossible; cases impossible) listEval
      (items := records.map (fun pair => .ref pair.1)) (by
        change Mutable.sequence (.ref (heap.length + 4)) base = _
        simp [Mutable.sequence, source]; rfl)
    simpa only [pairHeap, pairRefs, List.length_nil, List.range_zero, List.map_nil, List.append_nil,
      records, candidateRecords, List.drop_zero, List.map_cons, List.filter_cons, List.nil_append,
      neighbors, scopedEnv, neighborBody, comprehensionTargetName, comprehensionTargetBody,
      comprehensionFilters, comprehensionTargetsBody] using loop
  apply BlockReturns.function (args := neighborArgs) rfl rfl
  simpa [base, candidateHeap] using BlockReturns.return_value comprehension

theorem neighbors.complete (heap : Mutable.Heap) (r c : Int) (height width : Nat) :
    ∃ (extra : Mutable.Heap) (address : Nat) (rows : PairRows),
      ReturnsValue program "neighbors" [number r, number c, number height, number width] heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (rows.map (fun pair => .ref pair.1))) ∧
      (∀ pair ∈ rows, (heap ++ extra)[pair.1]? = some (.tuple (pairFields pair.2))) ∧
      rows.map Prod.snd = neighbors r c height width := by
  let base := candidateHeap heap r c
  let output := neighbors r c height width
  let extra := (candidates r c).map (fun pair => Mutable.Object.tuple (pairFields pair)) ++
    [.list (candidateRefs heap), .list (pairRefs base output.length)] ++ output.map (fun pair => .tuple (pairFields pair))
  have layout : heap ++ extra = pairHeap base output := by
    simp [extra, base, pairHeap, candidateHeap, List.append_assoc]
  refine ⟨extra, base.length, pairRecords base output, ?_, ?_, ?_, pair_records_values base output⟩
  · rw [layout]
    simpa [base, candidateHeap] using neighbors.result heap r c height width
  · rw [layout]
    exact pair_records_found base output
  · rw [layout]
    exact pair_records_read base output

end data.«project-euler-statements».data.py.project_euler_statements.p83
