import ProjectEulerStatements.Lib.MagicRingTextCalls

/-! The keyed minimum over outer-label indices selects the canonical rotation. -/
namespace ProjectEulerStatements.MagicRingIndexMinimumCalls
open FormalSW.PyAst HeapCalls MagicRing MagicRingTextCalls
set_option Elab.async false

def outerValue {n : Nat} (ring : Ring n) (index : Nat) : Nat := (ring.outer[index]?).getD 0
def cursor (poolAddress : Nat) (env : HeapCalls.Env) : SequenceExtremum :=
  ⟨false, .ref poolAddress, "index", .subscript (.name "outer") (.name "index"), env⟩

theorem read_index (heap : Mutable.Heap) (poolAddress n position : Nat) (inside : position < n)
    (pool : heap[poolAddress]? = some (.list (encode (List.range n)))) :
    extremumItem (.ref poolAddress) position heap = some (.ok (some (number position)), heap) := by
  simp [extremumItem, Mutable.sequence, pool, encode, List.getElem?_eq_getElem
    (show position < (List.range n).length by simpa using inside)]

theorem read_key (program : Module) {n : Nat} (ring : Ring n) (position : Nat)
    (inside : position < n) (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (localOuter : env "outer" = some (.ref outerAddress)) :
    Evaluates program (setLocal env "index" (number position))
      (.subscript (.name "outer") (.name "index")) heap (number (outerValue ring position)) heap :=
  index_evaluates program heap (setLocal env "index" (number position)) "outer"
    outerAddress position false ring.outer (outerValue ring position) (.name "index")
    (by simpa [setLocal] using localOuter) (Evaluates.lookup rfl)
    (by intros a b c impossible; cases impossible) getOuter
    (by simp only [outerValue,
      List.getElem?_eq_getElem (show position < ring.outer.length by
        rw [ring.outer_length]; exact inside), Option.getD_some])

theorem loop_result (program : Module) {n : Nat} (ring : Ring n) (position best : Nat)
    (before : position ≤ n) (inside : best < n)
    (least : ∀ index, index < position → outerValue ring best ≤ outerValue ring index)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress poolAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (pool : heap[poolAddress]? = some (.list (encode (List.range n))))
    (localOuter : env "outer" = some (.ref outerAddress)) :
    ExtremumReturns program (cursor poolAddress env) position
      (some (number best, number (outerValue ring best))) heap
      (number (minimumIndex ring.outer)) heap := by
  by_cases active : position < n
  · have read := read_index heap poolAddress n position active pool
    have key := read_key program ring position active heap env outerAddress getOuter localOuter
    by_cases smaller : outerValue ring position < outerValue ring best
    · have nextLeast : ∀ index, index < position + 1 →
          outerValue ring position ≤ outerValue ring index := by
        intro index bound
        by_cases earlier : index < position
        · exact (Nat.le_of_lt smaller).trans (least index earlier)
        · have same : index = position := by omega
          subst index
          exact Nat.le_refl _
      apply ExtremumReturns.next read key (afterSelection := heap)
        (updated := (number position, number (outerValue ring position)))
      · simp [SequenceExtremum.choose, cursor, HeapCalls.compare, scalarCompare, evalCmpOp,
          Mutable.truth, scalarTruth, number, smaller, Except.map]
      · exact loop_result program ring (position + 1) position (by omega) active nextLeast heap env
          outerAddress poolAddress getOuter pool localOuter
    · have nextLeast : ∀ index, index < position + 1 →
          outerValue ring best ≤ outerValue ring index := by
        intro index bound
        by_cases earlier : index < position
        · exact least index earlier
        · have same : index = position := by omega
          subst index
          exact Nat.le_of_not_gt smaller
      apply ExtremumReturns.next read key (afterSelection := heap)
        (updated := (number best, number (outerValue ring best)))
      · simp [SequenceExtremum.choose, cursor, HeapCalls.compare, scalarCompare, evalCmpOp,
          Mutable.truth, scalarTruth, number, smaller, Except.map]
      · exact loop_result program ring (position + 1) best (by omega) inside nextLeast heap env
          outerAddress poolAddress getOuter pool localOuter
  · have bestInside : best < ring.outer.length := by rw [ring.outer_length]; exact inside
    have minimum : minimumIndex ring.outer = best :=
      minimumIndex_unique ring.outer (outer_nodup ring) best bestInside (by
        intro value member
        obtain ⟨index, valid, rfl⟩ := List.getElem_of_mem member
        have bound : index < n := by simpa only [ring.outer_length] using valid
        simpa only [outerValue, List.getElem?_eq_getElem bestInside,
          List.getElem?_eq_getElem valid, Option.getD_some] using least index (by omega))
    rw [minimum]
    apply ExtremumReturns.done
    have empty : (encode (List.range n))[position]? = none :=
      List.getElem?_eq_none (by simp only [encode, List.length_map, List.length_range]; omega)
    simp [cursor, extremumItem, Mutable.sequence, pool, empty]
termination_by n - position
decreasing_by all_goals omega

theorem result (program : Module) {n : Nat} (ring : Ring n) (positive : 0 < n)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress poolAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (pool : heap[poolAddress]? = some (.list (encode (List.range n))))
    (localOuter : env "outer" = some (.ref outerAddress)) :
    ExtremumReturns program (cursor poolAddress env) 0 none heap
      (number (minimumIndex ring.outer)) heap := by
  apply ExtremumReturns.next (read_index heap poolAddress n 0 positive pool)
    (read_key program ring 0 positive heap env outerAddress getOuter localOuter)
    (afterSelection := heap) (updated := (number 0, number (outerValue ring 0)))
  · rfl
  · exact loop_result program ring 1 0 (by omega) positive
      (by
        intro index bound
        have same : index = 0 := by omega
        simpa only [same] using Nat.le_refl (outerValue ring 0))
      heap env outerAddress poolAddress getOuter pool localOuter

end ProjectEulerStatements.MagicRingIndexMinimumCalls
