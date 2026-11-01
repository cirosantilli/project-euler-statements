import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Digits
import lang.py.FormalSW.CombinationCalls
import Mathlib.Data.List.MinMax

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection consecutive_for_digits
set_option Elab.async false

abbrev program := P93Ast.module
def bestScore (best : Option (List Int)) : Int := best.elim (-1) (fun xs => runLength xs)
def nextBest (best : Option (List Int)) (candidate : List Int) : Option (List Int) :=
  if bestScore best < (runLength candidate : Int) then some candidate else best
def scan (candidates : List (List Int)) (best : Option (List Int)) : Option (List Int) :=
  candidates.foldl nextBest best

theorem nextBest_argAux (best : Option (List Int)) (candidate : List Int) :
    nextBest best candidate = List.argAux (fun a b => runLength b < runLength a) best candidate := by
  cases best with
  | none => simp [nextBest, bestScore, List.argAux]; omega
  | some xs => simp [nextBest, bestScore, List.argAux]

theorem scan_argmax (candidates : List (List Int)) : scan candidates none = candidates.argmax runLength := by
  have same : nextBest = List.argAux (fun a b => runLength b < runLength a) :=
    funext fun best => funext fun candidate => nextBest_argAux best candidate
  simp only [scan, List.argmax, same]

abbrev recordBody : List Stmt :=
  [.assign [.name "best_length"] (.name "length"), .assign [.name "best_digits"] (.name "digits")]
abbrev selectBody : List Stmt :=
  [.ifThen (.compare (.name "length") [(.gt, .name "best_length")]) recordBody []]
abbrev candidateBody : List Stmt :=
  .assign [.name "length"] (.call (.name "consecutive_for_digits") [.name "digits"]) :: selectBody

structure Ready (best : Option (List Int)) (heap : Mutable.Heap) (env : HeapCalls.Env) : Prop where
  score : env "best_length" = some (Heap.number (bestScore best))
  digits : ∃ address, env "best_digits" = some (.ref address) ∧
    heap[address]? = some (.tuple ((best.getD []).map Heap.number))

theorem Ready.append {best : Option (List Int)} {heap : Mutable.Heap} {env : HeapCalls.Env}
    (ready : Ready best heap env) (extra : Mutable.Heap) : Ready best (heap ++ extra) env := by
  obtain ⟨address, digits, found⟩ := ready.digits
  exact ⟨ready.score, address, digits, prefix_found heap extra address _ found⟩

/-- A strict score improvement replaces the winner; equal scores retain the earlier tuple. -/
theorem select_result (best : Option (List Int)) (candidate : List Int) (address : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (ready : Ready best heap env)
    (getLength : env "length" = some (Heap.number (runLength candidate)))
    (getDigits : env "digits" = some (.ref address))
    (input : heap[address]? = some (.tuple (candidate.map Heap.number))) :
    ∃ finalEnv, BlockContinues program env selectBody heap finalEnv heap globals ∧
      Ready (nextBest best candidate) heap finalEnv := by
  have test : Evaluates program env (.compare (.name "length") [(.gt, .name "best_length")])
      heap (.scalar (.bool (decide (bestScore best < (runLength candidate : Int))))) heap globals :=
    Evaluates.compare (Evaluates.lookup getLength) (Evaluates.lookup ready.score)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases improved : bestScore best < (runLength candidate : Int)
  · let afterScore := setLocal env "best_length" (Heap.number (runLength candidate))
    let afterDigits := setLocal afterScore "best_digits" (.ref address)
    refine ⟨afterDigits, ?_, ?_⟩
    · apply BlockContinues.branch (flag := true) test (by simp [improved, Mutable.truth, scalarTruth])
      exact (BlockContinues.assign (Evaluates.lookup getLength)).append
        (BlockContinues.assign (Evaluates.lookup (by simpa [afterScore, setLocal] using getDigits)))
    · rw [nextBest, if_pos improved]
      exact ⟨by simp [afterDigits, afterScore, setLocal, bestScore], address,
        by simp [afterDigits, setLocal], input⟩
  · refine ⟨env, BlockContinues.branch (flag := false) test
      (by simp [improved, Mutable.truth, scalarTruth]) .nil, ?_⟩
    simpa only [nextBest, if_neg improved] using ready

/-- One complete candidate score call followed by the strict best-score update. -/
theorem candidate_result (best : Option (List Int)) (candidate : List Int) (address : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (ready : Ready best heap env) (getDigits : env "digits" = some (.ref address))
    (input : heap[address]? = some (.tuple (candidate.map Heap.number))) :
    ∃ extra finalEnv, BlockContinues program env candidateBody heap finalEnv (heap ++ extra) globals ∧
      Ready (nextBest best candidate) (heap ++ extra) finalEnv := by
  obtain ⟨extra, counted⟩ := consecutive_for_digits.result candidate heap address globals input
  obtain ⟨bestAddress, getBest, foundBest⟩ := ready.digits
  let afterScore := setLocal env "length" (Heap.number (runLength candidate))
  have prepared : Ready best (heap ++ extra) afterScore :=
    ⟨by simpa [afterScore, setLocal] using ready.score, bestAddress,
      by simpa [afterScore, setLocal] using getBest,
      prefix_found heap extra bestAddress _ foundBest⟩
  obtain ⟨finalEnv, selected, finalReady⟩ := select_result best candidate address (heap ++ extra) afterScore globals
    prepared (by simp [afterScore, setLocal]) (by simpa [afterScore, setLocal] using getDigits)
    (prefix_found heap extra address _ input)
  refine ⟨extra, finalEnv, ?_, finalReady⟩
  exact (BlockContinues.assign (Evaluates.call (.cons (Evaluates.lookup getDigits) .nil) counted)).append selected

/-- The complete combination traversal implements the standard first-on-tie argmax fold. -/
theorem candidate_loop (candidates : List (List Int)) (best : Option (List Int)) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals) (ready : Ready best heap env) :
    ∃ extra finalEnv,
      BlockContinues program env [.permutationStepLoop "digits" (permutationSources candidates) candidateBody []]
        heap finalEnv (heap ++ extra) globals ∧ Ready (scan candidates best) (heap ++ extra) finalEnv := by
  induction candidates generalizing best heap env with
  | nil => exact ⟨[], env, by simpa using BlockContinues.permutation_done (module := program) .nil, by simpa [scan] using ready⟩
  | cons candidate candidates ih =>
    obtain ⟨bestAddress, getBest, foundBest⟩ := ready.digits
    obtain ⟨address, tupleExtra, allocated, foundTuple⟩ := allocate_tuple (candidate.map Heap.number) heap
    let bound := setLocal env "digits" (.ref address)
    have boundReady : Ready best (heap ++ tupleExtra) bound :=
      ⟨by simpa [bound, setLocal] using ready.score, bestAddress,
        by simpa [bound, setLocal] using getBest, prefix_found heap tupleExtra bestAddress _ foundBest⟩
    obtain ⟨scoreExtra, after, scored, afterReady⟩ := candidate_result best candidate address
      (heap ++ tupleExtra) bound globals boundReady (by simp [bound, setLocal]) foundTuple
    obtain ⟨later, finalEnv, continued, finalReady⟩ :=
      ih (nextBest best candidate) ((heap ++ tupleExtra) ++ scoreExtra) after afterReady
    refine ⟨tupleExtra ++ scoreExtra ++ later, finalEnv, ?_, ?_⟩
    · apply BlockContinues.permutation_step (tuple := .ref address) (middle := heap ++ tupleExtra)
      · simpa only [List.map_map, sequenceValue, sequenceSource] using allocated
      · simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, permutationSources,
          List.map_cons, List.append_assoc] using scored.append continued
    · simpa only [scan, List.foldl_cons, List.append_assoc] using finalReady

end data.«project-euler-statements».data.py.project_euler_statements.p93.naive
