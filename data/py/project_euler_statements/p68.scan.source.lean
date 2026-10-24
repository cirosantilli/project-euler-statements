import data.«project-euler-statements».data.py.project_euler_statements.«p68.candidate.source»
import lang.py.FormalSW.PermutationCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p68
open FormalSW.PyAst HeapCalls ProjectEulerStatements MagicRing MagicRingTextCalls
set_option Elab.async false

def capturedRows (rows : List (List Nat)) : List (List SequenceSource) :=
  rows.map (fun row => (encode row).map sequenceSource)

theorem permutations_result (n : Nat) (size : 2 ≤ n) (digits : Int) (rows : List (List Nat))
    (valid : ∀ row ∈ rows, row.Perm (labels n)) (best : String)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (ready : SearchReady n digits best env) :
    ∃ finalHeap, BlockReturns program env
      [.permutationStepLoop "values" (capturedRows rows) permutationBody [], .return (.name "best")]
      heap (string (referenceScan n digits rows best)) finalHeap := by
  induction rows generalizing best heap env with
  | nil =>
      refine ⟨heap, ?_⟩
      apply BlockReturns.permutation_done
      exact BlockReturns.return_value (Evaluates.lookup ready.getBest)
  | cons row rest ih =>
      obtain ⟨ring, packed, rowEq⟩ := pack_assignment n row (valid row List.mem_cons_self)
      have positive : 0 < row.length := by
        have length := (valid row List.mem_cons_self).length_eq
        simp only [labels, List.length_range'] at length
        omega
      have nonempty : (encode row).isEmpty = false := by
        apply List.isEmpty_eq_false_iff.mpr
        intro empty
        have length := congrArg List.length empty
        simp only [encode, List.length_map, List.length_nil] at length
        omega
      let tupleHeap := heap ++ [.tuple (encode row)]
      let rowEnv := setLocal env "values" (.ref heap.length)
      let next : Stmt := .permutationStepLoop "values" (capturedRows rest) permutationBody []
      have rowReady : SearchReady n digits best rowEnv := by
        constructor
        · simpa [rowEnv, setLocal] using ready.getN
        · simpa [rowEnv, setLocal] using ready.getDigits
        · simpa [rowEnv, setLocal] using ready.getBest
      have rowBest : rowVisit n digits best row = visit ring digits best := by
        rw [rowVisit, packed]
      have post (nextEnv : HeapCalls.Env) (nextHeap : Mutable.Heap)
          (nextReady : SearchReady n digits (visit ring digits best) nextEnv) :
          ∃ finalHeap, BlockReturns program nextEnv [next, .return (.name "best")]
            nextHeap (string (referenceScan n digits (row :: rest) best)) finalHeap := by
        obtain ⟨finalHeap, continued⟩ := ih
          (fun entry member => valid entry (List.mem_cons_of_mem _ member))
          (visit ring digits best) nextHeap nextEnv nextReady
        exact ⟨finalHeap, by simpa only [referenceScan_cons, rowBest] using continued⟩
      obtain ⟨finalHeap, advanced⟩ := candidate_result ring size digits best tupleHeap rowEnv
        heap.length (by simp [tupleHeap, rowEq]) rfl rowReady next [.return (.name "best")]
        (string (referenceScan n digits (row :: rest) best)) post
      refine ⟨finalHeap, ?_⟩
      apply BlockReturns.permutation_step
        (tuple := .ref heap.length) (middle := tupleHeap)
      · simp [List.map_map, Function.comp_def, Mutable.allocateTuple, nonempty, tupleHeap,
          Except.map]
      · exact advanced

end data.«project-euler-statements».data.py.project_euler_statements.p68
