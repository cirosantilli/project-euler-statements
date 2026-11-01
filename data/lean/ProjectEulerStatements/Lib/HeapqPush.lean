import ProjectEulerStatements.Lib.MinHeapRise
import lang.py.FormalSW.HeapqContents
import Mathlib.Data.String.Basic

/-! Ordering guarantees for the concrete upward sift and heap push.
The comparison law connects stored values to any linearly ordered alphabet;
the proofs retain the actual swaps and the exact caller heap frame. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

def EncodesOrder (encode : α → Mutable.Value) : Prop :=
  ∀ heap left right, Heapq.less (encode left) (encode right) heap =
    some (.ok (decide (left < right)), heap)

theorem strings_encodeOrder : EncodesOrder (fun text : String => .scalar (.string text)) := by
  intro heap left right
  rw [Heapq.less_string]
  congr 3
  simp only [String.lt_iff, lt_iff_le_not_ge, String.le_iff_toList_le]

theorem integers_encodeOrder : EncodesOrder (fun number : Int => .scalar (.int number)) :=
  fun heap left right => Heapq.less_int heap left right

theorem siftDown_root_ordered (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address position : Nat) (values : List α)
    (inside : position < values.length) (rising : Rising values position)
    (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.siftDown address 0 position heap =
        some (.ok (), heap.set address (.list (changed.map encode))) ∧
      changed.Perm values ∧ Ordered changed := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  have unchanged : heap.set address (.list (values.map encode)) = heap := by
    obtain ⟨bounded, entry⟩ := List.getElem?_eq_some_iff.mp found
    rw [← entry, List.set_getElem_self bounded]
  by_cases zero : position = 0
  · subst position
    exact ⟨values, by simpa [unchanged] using Heapq.siftDown_stop heap address 0 0 (by omega),
      .refl _, rising.root values⟩
  · have positive : 0 < position := by omega
    let parent := (position - 1) / 2
    have smaller : parent < position := by
      have := Nat.div_le_self (position - 1) 2
      dsimp [parent]
      omega
    have parentInside := Nat.lt_trans smaller inside
    have edge : Child parent position := by unfold Child; dsimp [parent]; omega
    have readValue : Heapq.atIndex address position heap =
        some (.ok (encode values[position]), heap) := by
      rw [Heapq.atIndex_list heap address position (values.map encode) found (by simpa)]
      rw [List.getElem_map encode]
    have readParent : Heapq.atIndex address parent heap =
        some (.ok (encode values[parent]), heap) := by
      rw [Heapq.atIndex_list heap address parent (values.map encode) found (by simpa)]
      rw [List.getElem_map encode]
    have compared := comparison heap values[position] values[parent]
    by_cases less : values[position] < values[parent]
    · let exchanged := (values.set position values[parent]).set parent values[position]
      have permutation : exchanged.Perm values :=
        Heapq.swap_contents_perm values position parent inside parentInside
      have newRising : Rising exchanged parent :=
        rising.swap values position parent inside parentInside edge less
      obtain ⟨changed, finished, contents, ordered⟩ := siftDown_root_ordered encode comparison
        (heap.set address (.list (exchanged.map encode))) address parent exchanged
        (by rw [permutation.length_eq]; exact parentInside) newRising (by simp [valid])
      simp [exchanged, parent] at finished
      refine ⟨changed, ?_, contents.trans permutation, ordered⟩
      rw [Heapq.siftDown]
      simp [positive, readValue, readParent, compared, less,
        Heapq.swap_mapped_list encode heap address position parent values found inside parentInside,
        finished, parent]
    · refine ⟨values, ?_, .refl _, rising.settled values position parent inside parentInside
        edge (le_of_not_gt less)⟩
      rw [unchanged, Heapq.siftDown]
      simp [positive, readValue, readParent, compared, less, parent]
termination_by position
decreasing_by exact smaller

/-- Appending and sifting an element produces an ordered permutation of all entries. -/
theorem heappush_ordered (encode : α → Mutable.Value) (comparison : EncodesOrder encode)
    (heap : Mutable.Heap) (address : Nat) (values : List α) (value : α)
    (ordered : Ordered values) (found : heap[address]? = some (.list (values.map encode))) :
    ∃ changed, Heapq.heappush [.ref address, encode value] heap =
        some (.ok (.scalar .none), heap.set address (.list (changed.map encode))) ∧
      changed.Perm (values ++ [value]) ∧ Ordered changed := by
  have valid := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨changed, finished, contents, resultOrdered⟩ := siftDown_root_ordered encode comparison
    (heap.set address (.list ((values ++ [value]).map encode))) address values.length
    (values ++ [value]) (by simp) (Rising.append values value ordered) (by simp [valid])
  refine ⟨changed, ?_, contents, resultOrdered⟩
  apply Heapq.heappush_result heap _ address (values.map encode) (encode value) (.ok ()) found
  simpa using finished

end ProjectEulerStatements.MinHeap
