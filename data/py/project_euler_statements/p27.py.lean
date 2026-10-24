import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p27.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerStatements.Lib.QuadraticPrimes
import ProjectEulerStatements.Lib.ArgMaximum
import FormalSW
import Mathlib.Data.List.Forall2

namespace data.«project-euler-statements».data.py.project_euler_statements.p27
open FormalSW.PyAst
open ProjectEulerStatements.P27 ProjectEulerStatements.QuadraticPrimes
private abbrev program := P27Ast.module


private theorem common_extension : Calls.Extends program CommonAst.module := by
  change Calls.Extends { body := program.body.take 6 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["quad", "is_prime_int", "consec_prime_len", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

section Scalar
open Calls

theorem quad.result (a b : Int) (n : Nat) :
    ReturnsValue program "quad" [.int a, .int b, .int n] (.int (quad a b n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary
    (Evaluates.binary
      (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl)
      (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl) rfl)
    (Evaluates.lookup rfl) rfl

theorem is_prime_int.result (z : Int) :
    ReturnsValue program "is_prime_int" [.int z] (.bool (isPrimeInt z)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases positive : 1 < z
  · simp only [isPrimeInt, positive, decide_true, Bool.true_and]
    apply Evaluates.boolean_continue (first := .bool true)
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
        (by simp [scalarCompare, evalCmpOp, positive])) rfl
    apply Evaluates.boolean_last
    apply Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
    simpa [Int.toNat_of_nonneg (by omega : 0 ≤ z)] using
      (common.is_prime.result z.toNat).extend common_extension
  · simp only [isPrimeInt, positive, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop
      (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
        (by simp [scalarCompare, evalCmpOp, positive])) rfl

private def countLoop : List Stmt :=
  (executableBody ((findFunctionIn program.body "consec_prime_len").getD ([], [])).2).drop 2

private theorem count_loop (a b : Int) (n : Nat) (before : n ≤ first a b)
    (env : ScalarEnv) (getA : env "a" = some (.int a)) (getB : env "b" = some (.int b))
    (getBound : env "bound" = some (.int (consecPrimeBound b)))
    (getN : env "n" = some (.int n)) :
    BlockReturns program env countLoop (.int (first a b)) := by
  induction measure : first a b - n using Nat.strong_induction_on generalizing n env with
  | h size ih =>
      have bound : n < consecPrimeBound b := lt_of_le_of_lt before (first_lt_bound a b)
      have tested : Evaluates program env
          (.boolOp .and [.compare (.name "n") [(.lt, .name "bound")],
            .call (.name "is_prime_int") [.call (.name "quad") [.name "a", .name "b", .name "n"]]])
          (.bool (isPrimeInt (quad a b n))) := by
        apply Evaluates.boolean_continue (first := .bool true)
          (Evaluates.compare (Evaluates.lookup getN) (Evaluates.lookup getBound)
            (by simp [scalarCompare, evalCmpOp, bound])) rfl
        apply Evaluates.boolean_last
        exact Evaluates.call (.cons
          (Evaluates.call (.cons (Evaluates.lookup getA) (.cons (Evaluates.lookup getB)
            (.cons (Evaluates.lookup getN) .nil))) (quad.result a b n)) .nil)
          (is_prime_int.result (quad a b n))
      by_cases same : n = first a b
      · apply BlockReturns.while_loop (value := .bool false)
        · simpa [same, first_spec] using tested
        · exact BlockReturns.return_value (Evaluates.lookup (by simpa [same] using getN))
      · have smaller : n < first a b := by omega
        apply BlockReturns.while_loop (value := .bool true)
        · simpa [before_first a b n smaller] using tested
        · apply BlockReturns.augAssign (value := .int (n + 1))
          · exact Evaluates.binary (Evaluates.lookup getN) Evaluates.constant (by simp [scalarBinary])
          · apply ih (first a b - (n + 1)) (by omega) (n + 1) (by omega)
            all_goals simp [ScalarEnv.set, getA, getB, getBound]

theorem consec_prime_len.result (a b : Int) :
    ReturnsValue program "consec_prime_len" [.int a, .int b] (.int (consecPrimeLen a b)) := by
  rw [consecPrimeLen_eq_first]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .int (consecPrimeBound b))
  · exact Evaluates.binary
      (Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) rfl) Evaluates.constant rfl
  · apply BlockReturns.assign Evaluates.constant
    exact count_loop a b 0 (by omega) _ rfl rfl rfl rfl

theorem consec_prime_len.«Returns» (a b : Int) :
    (Calls.function program "consec_prime_len" [.int a, .int b]).Returns :=
  (consec_prime_len.result a b).returns

end Scalar


namespace HeapHelpers
open HeapCalls
private abbrev num (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

private def Trial (n r p : Nat) : Prop := ∀ q ∈ Finset.Icc p r, q % 2 = 1 → ¬ q ∣ n
private instance (n r p : Nat) : Decidable (Trial n r p) := by unfold Trial; infer_instance

private theorem trial_step (n r p : Nat) (hle : p ≤ r) (odd : p % 2 = 1) :
    Trial n r p ↔ ¬p ∣ n ∧ Trial n r (p + 2) := by
  simp only [Trial, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨h p ⟨le_rfl, hle⟩ odd, fun q hq hodd => h q ⟨by omega, hq.2⟩ hodd⟩
  · rintro ⟨hp, h⟩ q hq hodd
    by_cases heq : q = p
    · simpa [heq] using hp
    · exact h q ⟨by omega, hq.2⟩ hodd

private theorem trial_prime (n : Nat) (hn : 2 ≤ n) (odd : n % 2 ≠ 0) :
    Trial n (Math.isqrt n) 3 ↔ Nat.Prime n := by
  have root : Math.isqrt n = Nat.sqrt n := Nat.eq_sqrt.mpr (Math.isqrt_spec n)
  rw [root, Nat.prime_def_le_sqrt]
  constructor
  · intro h
    refine ⟨hn, fun q hq hroot hdvd => ?_⟩
    by_cases even : q % 2 = 0
    · exact odd (Nat.dvd_iff_mod_eq_zero.mp (dvd_trans (Nat.dvd_iff_mod_eq_zero.mpr even) hdvd))
    · exact h q (Finset.mem_Icc.mpr ⟨by omega, hroot⟩) (by omega) hdvd
  · rintro ⟨_, h⟩ q hq _
    exact h q (by have := (Finset.mem_Icc.mp hq).1; omega) (Finset.mem_Icc.mp hq).2

private def primeLoop : List Stmt :=
  (executableBody ((findFunctionIn program.body "is_prime").getD ([], [])).2).drop 5

private theorem prime_loop (n r p : Nat) (positive : 0 < p) (odd : p % 2 = 1)
    (env : HeapCalls.Env) (getN : env "n" = some (num n)) (getR : env "r" = some (num r))
    (getP : env "p" = some (num p)) (heap : Heap) :
    BlockReturns program env primeLoop heap (flag (decide (Trial n r p))) heap := by
  induction measure : r + 1 - p using Nat.strong_induction_on generalizing p env with
  | h size ih =>
      by_cases inside : p ≤ r
      · apply BlockReturns.while_loop (middle := heap) (flag := true) (value := flag true)
          (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup getP) (Evaluates.lookup getR)
            (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, inside])) rfl
        have divides : Evaluates program env
            (.compare (.binOp (.name "n") .mod (.name "p")) [(.eq, .constant (.int 0))])
            heap (flag (decide (p ∣ n))) heap := by
          apply Evaluates.compare (middle := heap) (afterRight := heap) (av := num (n % p)) (bv := num 0)
          · exact Evaluates.binary (finalHeap := heap) (Evaluates.lookup getN) (Evaluates.lookup getP)
              (by simp [Mutable.binary, num, scalarBinary, positive.ne', positive])
          · exact Evaluates.constant
          · simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, ← Int.dvd_iff_emod_eq_zero, Int.natCast_dvd_natCast]
        by_cases divisor : p ∣ n
        · have bad : ¬ Trial n r p := fun h => ((trial_step n r p inside odd).mp h).1 divisor
          simp only [bad, decide_false]
          apply BlockReturns.branch (middle := heap) (flag := true) (value := flag true) (by simpa [divisor] using divides) rfl
          exact BlockReturns.return_value Evaluates.constant
        · simp only [trial_step n r p inside odd, divisor, not_false_eq_true, true_and]
          apply BlockReturns.branch (middle := heap) (flag := false) (value := flag false) (by simpa [divisor] using divides) rfl
          apply BlockReturns.augAssign (value := num (p + 2)) (afterOperation := heap)
            getP Evaluates.constant
          · simp [inplace, Mutable.binary, num, scalarBinary]
          · apply ih (r + 1 - (p + 2)) (by omega) (p + 2) (by omega) (by omega)
            all_goals simp [setLocal, getN, getR]
      · have good : Trial n r p := by
          intro q hq _
          have := Finset.mem_Icc.mp hq
          omega
        simp only [good, decide_true]
        apply BlockReturns.while_loop (middle := heap) (flag := false) (value := flag false)
          (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup getP) (Evaluates.lookup getR)
            (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, inside])) rfl
        exact BlockReturns.return_value Evaluates.constant

private theorem prime_small (n : Int) (small : n < 2) (heap : Heap) :
    ReturnsValue program "is_prime" [num n] heap (flag false) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (middle := heap) (flag := true) (value := flag true)
    (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
      (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, small])) rfl
  exact BlockReturns.return_value Evaluates.constant

/-- The imported trial-division source is pure even when invoked from heap code. -/
theorem prime_result (n : Nat) (heap : Heap) :
    ReturnsValue program "is_prime" [num n] heap (flag (decide (Nat.Prime n))) heap := by
  by_cases small : n < 2
  · have bad : ¬ Nat.Prime n := fun prime => by have := prime.two_le; omega
    simpa [bad] using prime_small n (by omega) heap
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (middle := heap) (flag := false) (value := flag false)
    (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
      (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp]; omega)) rfl
  by_cases two : n = 2
  · subst n
    simp only [Nat.prime_two, decide_true]
    apply BlockReturns.branch (middle := heap) (flag := true) (value := flag true)
      (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant rfl) rfl
    exact BlockReturns.return_value Evaluates.constant
  · apply BlockReturns.branch (middle := heap) (flag := false) (value := flag false)
      (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
        (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp]; omega)) rfl
    have parity : Evaluates program
        (argumentEnv [{ name := "n", annotation := some (.name "int") }] [num n])
        (.compare (.binOp (.name "n") .mod (.constant (.int 2))) [(.eq, .constant (.int 0))])
        heap (flag (decide (n % 2 = 0))) heap := by
      apply Evaluates.compare (middle := heap) (afterRight := heap) (av := num (n % 2)) (bv := num 0)
      · exact Evaluates.binary (finalHeap := heap) (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, num, scalarBinary])
      · exact Evaluates.constant
      · simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, ← Int.dvd_iff_emod_eq_zero, Int.ofNat_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
    by_cases even : n % 2 = 0
    · have bad : ¬ Nat.Prime n := fun prime => by have := prime.eq_two_or_odd; omega
      simp only [bad, decide_false]
      apply BlockReturns.branch (middle := heap) (flag := true) (value := flag true) (by simpa [even] using parity) rfl
      exact BlockReturns.return_value Evaluates.constant
    · apply BlockReturns.branch (middle := heap) (flag := false) (value := flag false) (by simpa [even] using parity) rfl
      apply BlockReturns.assign (value := num (Math.isqrt n)) (middle := heap)
      · apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
        change scalarResult (some (Math.isqrtCall [.int n])) heap = _
        simp [Math.isqrtCall, scalarResult, num, show ¬ (n : Int) < 0 by omega]
      · apply BlockReturns.assign Evaluates.constant
        simpa [trial_prime n (by omega) even] using
          prime_loop n (Math.isqrt n) 3 (by decide) (by decide) _ rfl rfl rfl heap

end HeapHelpers


namespace HeapHelpers
open HeapCalls

theorem quad_result (a b : Int) (n : Nat) (heap : Heap) :
    ReturnsValue program "quad" [num a, num b, num n] heap (num (quad a b n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.binary
    (Evaluates.binary
      (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl)
      (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl) rfl)
    (Evaluates.lookup rfl) rfl

theorem is_prime_int_result (z : Int) (heap : Heap) :
    ReturnsValue program "is_prime_int" [num z] heap (flag (isPrimeInt z)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases positive : 1 < z
  · simp only [isPrimeInt, positive, decide_true, Bool.true_and]
    apply Evaluates.boolean_next (value := flag true) (flag := true) (middle := heap)
      (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
        (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, positive])) rfl rfl
    apply Evaluates.boolean_last (flag := decide (Nat.Prime z.toNat))
    · apply Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      simpa [num, Int.toNat_of_nonneg (by omega : 0 ≤ z)] using prime_result z.toNat heap
    · rfl
  · simp only [isPrimeInt, positive, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop (flag := false)
      (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
        (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, positive])) rfl rfl

private theorem count_loop (a b : Int) (n : Nat) (before : n ≤ first a b)
    (env : HeapCalls.Env) (getA : env "a" = some (num a)) (getB : env "b" = some (num b))
    (getBound : env "bound" = some (num (consecPrimeBound b)))
    (getN : env "n" = some (num n)) (heap : Heap) :
    BlockReturns program env countLoop heap (num (first a b)) heap := by
  induction measure : first a b - n using Nat.strong_induction_on generalizing n env with
  | h size ih =>
      have bound : n < consecPrimeBound b := lt_of_le_of_lt before (first_lt_bound a b)
      have tested : Evaluates program env
          (.boolOp .and [.compare (.name "n") [(.lt, .name "bound")],
            .call (.name "is_prime_int") [.call (.name "quad") [.name "a", .name "b", .name "n"]]])
          heap (flag (isPrimeInt (quad a b n))) heap := by
        apply Evaluates.boolean_next (value := flag true) (flag := true) (middle := heap)
          (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup getN) (Evaluates.lookup getBound)
            (by simp [HeapCalls.compare, flag, scalarCompare, evalCmpOp, bound])) rfl rfl
        apply Evaluates.boolean_last (flag := isPrimeInt (quad a b n))
        · exact Evaluates.call (.cons
            (Evaluates.call (.cons (Evaluates.lookup getA) (.cons (Evaluates.lookup getB)
              (.cons (Evaluates.lookup getN) .nil))) (quad_result a b n heap)) .nil)
            (is_prime_int_result (quad a b n) heap)
        · rfl
      by_cases same : n = first a b
      · apply BlockReturns.while_loop (flag := false) (value := flag false) (middle := heap)
          (by simpa [same, first_spec] using tested) rfl
        exact BlockReturns.return_value (Evaluates.lookup (by simpa [same] using getN))
      · have smaller : n < first a b := by omega
        apply BlockReturns.while_loop (flag := true) (value := flag true) (middle := heap)
          (by simpa [before_first a b n smaller] using tested) rfl
        apply BlockReturns.augAssign (value := num (n + 1)) (afterOperation := heap) getN Evaluates.constant
        · simp [inplace, Mutable.binary, num, scalarBinary]
        · apply ih (first a b - (n + 1)) (by omega) (n + 1) (by omega)
          all_goals simp [setLocal, getA, getB, getBound]

theorem consec_result (a b : Int) (heap : Heap) :
    ReturnsValue program "consec_prime_len" [num a, num b] heap (num (consecPrimeLen a b)) heap := by
  rw [consecPrimeLen_eq_first]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := num (consecPrimeBound b)) (middle := heap)
  · exact Evaluates.binary
      (Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) rfl) Evaluates.constant rfl
  · apply BlockReturns.assign Evaluates.constant
    exact count_loop a b 0 (by omega) _ rfl rfl rfl rfl heap

end HeapHelpers

/-- Heap callers receive the exact prime-prefix length without altering any existing object. -/
theorem consec_prime_len.heap_result (a b : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "consec_prime_len" [.scalar (.int a), .scalar (.int b)] heap
      (.scalar (.int (consecPrimeLen a b))) heap := HeapHelpers.consec_result a b heap


namespace ReferenceHeap
open HeapCalls
private abbrev num (n : Int) : Mutable.Value := .scalar (.int n)
private def pairValues (p : Int × Int) : List Mutable.Value := [num p.1, num p.2]
private theorem inside {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) : address < heap.length := by
  by_contra invalid
  rw [List.getElem?_eq_none (by omega)] at found
  cases found
private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (tail : Mutable.Heap) :
    (heap ++ tail)[address]? = some object := by
  rw [List.getElem?_append_left (inside found)]
  exact found
private def Preserves (before after : Mutable.Heap) (collector : Nat) : Prop :=
  ∀ address object, address ≠ collector → before[address]? = some object → after[address]? = some object
private theorem Preserves.trans (first : Preserves before middle collector)
    (second : Preserves middle after collector) : Preserves before after collector :=
  fun address object other found => second address object other (first address object other found)
private theorem appended (heap tail : Mutable.Heap) (collector : Nat) : Preserves heap (heap ++ tail) collector :=
  fun _ _ _ found => found_append found tail
private theorem updated (heap : Mutable.Heap) (collector : Nat) (object : Mutable.Object) :
    Preserves heap (heap.set collector object) collector := by
  intro address item other found
  simpa [List.getElem?_set_ne other.symm] using found
private def Rows (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (pairs : List (Int × Int)) : Prop :=
  List.Forall₂ (fun address pair => collector < address ∧ heap[address]? = some (.tuple (pairValues pair))) addresses pairs
private theorem Rows.preserve (rows : Rows before collector addresses pairs)
    (preserved : Preserves before after collector) : Rows after collector addresses pairs := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1, preserved _ _ (by omega) head.2⟩ ih
private abbrev emit (collector : Nat) : List Stmt :=
  [.comprehensionAppend collector (.tuple [.name "a", .name "b"])]
private theorem append_pair (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat)
    (pairs : List (Int × Int)) (env : HeapCalls.Env) (a b : Int)
    (getA : env "a" = some (num a)) (getB : env "b" = some (num b))
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses pairs) :
    ∃ finalHeap,
      BlockContinues program env (emit collector) heap env finalHeap ∧
      finalHeap[collector]? = some (.list ((addresses ++ [heap.length]).map Mutable.Value.ref)) ∧
      Rows finalHeap collector (addresses ++ [heap.length]) (pairs ++ [(a,b)]) ∧
      Preserves heap finalHeap collector := by
  let nextAddresses := addresses ++ [heap.length]
  let nextHeap : Mutable.Heap := (heap ++ [Mutable.Object.tuple (pairValues (a,b))]).set collector (.list (nextAddresses.map Mutable.Value.ref))
  have bound := inside found
  have emitted : BlockContinues program env (emit collector) heap env nextHeap := by
    have tuple := Evaluates.tuple (module := program) (globals := []) (heap := heap)
      (.cons (Evaluates.lookup getA) (.cons (Evaluates.lookup getB) .nil)) (by simp)
    simpa [nextHeap, nextAddresses, emit, pairValues] using
      BlockContinues.comprehension_append tuple (found_append found [.tuple (pairValues (a,b))])
  have nextFound : nextHeap[collector]? = some (.list (nextAddresses.map Mutable.Value.ref)) := by
    apply List.getElem?_set_self
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have preserved : Preserves heap nextHeap collector :=
    (appended heap [.tuple (pairValues (a,b))] collector).trans (updated _ collector _)
  have fresh : collector < heap.length ∧ nextHeap[heap.length]? = some (.tuple (pairValues (a,b))) := by
    refine ⟨bound, ?_⟩
    change ((heap ++ [Mutable.Object.tuple (pairValues (a,b))]).set collector _)[heap.length]? = _
    rw [List.getElem?_set_ne (by omega : collector ≠ heap.length)]
    simp
  exact ⟨nextHeap, emitted, nextFound, List.rel_append (rows.preserve preserved) (.cons fresh .nil), preserved⟩

/-- A finite ascending integer interval, including empty Python ranges. -/
private def interval (start : Int) : Nat → List Int
  | 0 => []
  | n+1 => start :: interval (start+1) n
private theorem collect_inner (count : Nat) (start stop a limitB : Int)
    (length : (stop-start).toNat = count) (heap : Mutable.Heap)
    (collector : Nat) (addresses : List Nat) (before : List (Int × Int)) (env : HeapCalls.Env)
    (getA : env "a" = some (num a)) (getLimit : env "limit_b" = some (num limitB))
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "b" start stop 1 (emit collector) []] heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before ++ (interval start count).map (a, ·)) ∧
      finalEnv "a" = some (num a) ∧ finalEnv "limit_b" = some (num limitB) ∧
      Preserves heap finalHeap collector := by
  induction count generalizing start heap addresses before env with
  | zero =>
      have finished : stop ≤ start := by omega
      refine ⟨heap, env, addresses, BlockContinues.range_done ?_ .nil, found, ?_, getA, getLimit, ?_⟩
      · simp [Calls.rangeContinues, not_lt.mpr finished]
      · simpa [interval] using rows
      · exact fun _ _ _ h => h
  | succ count ih =>
      have continues : start < stop := by omega
      let bound := setLocal env "b" (num start)
      obtain ⟨nextHeap, emitted, nextFound, nextRows, preserved⟩ :=
        append_pair heap collector addresses before bound a start (by simpa [bound, setLocal] using getA) rfl found rows
      obtain ⟨finalHeap, finalEnv, finalAddresses, executed, finalFound, finalRows, finalA, finalB, saved⟩ :=
        ih (start+1) (by omega) nextHeap (addresses ++ [heap.length]) (before ++ [(a,start)]) bound
          (by simpa [bound, setLocal] using getA) (by simpa [bound, setLocal] using getLimit) nextFound nextRows
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_, finalA, finalB, preserved.trans saved⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues, continues])
        simpa [emit, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, bound] using emitted.append executed
      · simpa [interval, List.append_assoc] using finalRows

private abbrev innerBody (collector : Nat) : List Stmt :=
  [.forIn (.name "b") (.call (.name "range")
    [.unaryOp .uSub (.name "limit_b"), .binOp (.name "limit_b") .add (.constant (.int 1))]) (emit collector) []]
private theorem collect_outer (count : Nat) (start stop limitB : Int)
    (length : (stop-start).toNat = count) (heap : Mutable.Heap)
    (collector : Nat) (addresses : List Nat) (before : List (Int × Int)) (env : HeapCalls.Env)
    (getLimit : env "limit_b" = some (num limitB))
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "a" start stop 1 (innerBody collector) []] heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses
        (before ++ (interval start count).flatMap (fun a => (interval (-limitB) (2*limitB+1).toNat).map (a, ·))) ∧
      finalEnv "limit_b" = some (num limitB) ∧ Preserves heap finalHeap collector := by
  induction count generalizing start heap addresses before env with
  | zero =>
      have finished : stop ≤ start := by omega
      refine ⟨heap, env, addresses, BlockContinues.range_done ?_ .nil, found, ?_, getLimit, ?_⟩
      · simp [Calls.rangeContinues, not_lt.mpr finished]
      · simpa [interval] using rows
      · exact fun _ _ _ h => h
  | succ count ih =>
      have continues : start < stop := by omega
      let bound := setLocal env "a" (num start)
      have boundLimit : bound "limit_b" = some (num limitB) := by simpa [bound, setLocal] using getLimit
      obtain ⟨nextHeap, nextEnv, nextAddresses, inner, nextFound, nextRows, _, nextLimit, preserved⟩ :=
        collect_inner (2*limitB+1).toNat (-limitB) (limitB+1) start limitB
          (by congr 1; omega) heap collector addresses before bound rfl boundLimit found rows
      have innerExecuted : BlockContinues program bound (innerBody collector) heap nextEnv nextHeap := by
        apply BlockContinues.for_range (middle := heap) (values := [num (-limitB), num (limitB+1)])
        · exact .cons (Evaluates.unary (Evaluates.lookup boundLimit) rfl)
            (.cons (Evaluates.binary (Evaluates.lookup boundLimit) Evaluates.constant rfl) .nil)
        · rfl
        · exact inner
      obtain ⟨finalHeap, finalEnv, finalAddresses, executed, finalFound, finalRows, finalLimit, saved⟩ :=
        ih (start+1) (by omega) nextHeap nextAddresses
          (before ++ (interval (-limitB) (2*limitB+1).toNat).map (start, ·)) nextEnv nextLimit nextFound nextRows
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_, finalLimit, preserved.trans saved⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues, continues])
        simpa [innerBody, emit, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, bound] using innerExecuted.append executed
      · simpa [interval, List.append_assoc] using finalRows
private abbrev pairExpression : Expr :=
  .listComp (.tuple [.name "a", .name "b"])
    [("a", .call (.name "range") [.unaryOp .uSub (.name "limit_a"), .binOp (.name "limit_a") .add (.constant (.int 1))], []),
     ("b", .call (.name "range") [.unaryOp .uSub (.name "limit_b"), .binOp (.name "limit_b") .add (.constant (.int 1))], [])]
private def pairs (a b : Int) : List (Int × Int) :=
  (interval (-a) (2*a+1).toNat).flatMap (fun x => (interval (-b) (2*b+1).toNat).map (x, ·))
private theorem collect_pairs (heap : Mutable.Heap) (env : HeapCalls.Env) (a b : Int)
    (getA : env "limit_a" = some (num a)) (getB : env "limit_b" = some (num b)) :
    ∃ finalHeap addresses,
      Evaluates program env pairExpression heap (.ref heap.length) finalHeap ∧
      finalHeap[heap.length]? = some (.list (addresses.map Mutable.Value.ref)) ∧
      Rows finalHeap heap.length addresses (pairs a b) := by
  obtain ⟨finalHeap, finalEnv, addresses, executed, found, rows, _, _⟩ :=
    collect_outer (2*a+1).toNat (-a) (a+1) b (by congr 1; omega)
      (heap ++ [.list []]) heap.length [] []
      (comprehensionEnv env [("a", .call (.name "range") [.unaryOp .uSub (.name "limit_a"), .binOp (.name "limit_a") .add (.constant (.int 1))], []),
       ("b", .call (.name "range") [.unaryOp .uSub (.name "limit_b"), .binOp (.name "limit_b") .add (.constant (.int 1))], [])])
      (by simpa [comprehensionEnv] using getB) (by simp) .nil
  refine ⟨finalHeap, addresses, ?_, found, ?_⟩
  · apply Evaluates.list_comp_range (middle := heap) (values := [num (-a), num (a+1)])
    · exact .cons (Evaluates.unary (Evaluates.lookup getA) rfl)
        (.cons (Evaluates.binary (Evaluates.lookup getA) Evaluates.constant rfl) .nil)
    · rfl
    · exact executed
  · simpa [pairs] using rows

private abbrev keyExpression : Expr :=
  .call (.name "consec_prime_len")
    [.subscript (.name "p") (.constant (.int 0)), .subscript (.name "p") (.constant (.int 1))]
private def score (p : Int × Int) : Nat := consecPrimeLen p.1 p.2
private theorem key_result (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat) (p : Int × Int)
    (getP : env "p" = some (.ref address)) (found : heap[address]? = some (.tuple (pairValues p))) :
    Evaluates program env keyExpression heap (num (score p)) heap := by
  apply Evaluates.call (middle := heap) (values := [num p.1, num p.2])
  · refine .cons (middle := heap) ?_ (.cons (middle := heap) ?_ .nil)
    · apply Evaluates.subscript (middle := heap) (afterIndex := heap)
        (by intros; intro h; cases h) (Evaluates.lookup getP) Evaluates.constant
      simp [Mutable.getItem, found, pairValues, Mutable.index, num, Except.map]
    · apply Evaluates.subscript (middle := heap) (afterIndex := heap)
        (by intros; intro h; cases h) (Evaluates.lookup getP) Evaluates.constant
      simp [Mutable.getItem, found, pairValues, Mutable.index, num, Except.map]
  · exact consec_prime_len.heap_result p.1 p.2 heap

private abbrev cursor (env : HeapCalls.Env) (collector : Nat) : SequenceExtremum :=
  ⟨true, .ref collector, "p", keyExpression, env⟩
private theorem scan_max (heap : Mutable.Heap) (env : HeapCalls.Env) (collector : Nat)
    (all : List Nat) (position : Nat) (remaining : List Nat) (values : List (Int × Int))
    (found : heap[collector]? = some (.list (all.map Mutable.Value.ref)))
    (suffix : all.drop position = remaining) (rows : Rows heap collector remaining values)
    (bestAddress : Nat) (best : Int × Int) (bestFound : heap[bestAddress]? = some (.tuple (pairValues best))) :
    ∃ address,
      ExtremumReturns program (cursor env collector) position (some (.ref bestAddress, num (score best)))
        heap (.ref address) heap ∧
      heap[address]? = some (.tuple (pairValues (values.foldl (ProjectEulerStatements.ArgMaximum.select score) best))) := by
  induction rows generalizing position bestAddress best with
  | nil =>
      refine ⟨bestAddress, ExtremumReturns.done ?_, bestFound⟩
      have index : all[position]? = none := by
        have := congrArg (fun xs : List Nat => xs[0]?) suffix
        simpa using this
      simp [extremumItem, Mutable.sequence, found, List.getElem?_map, index]
  | @cons address pair addresses values head tail ih =>
      have index : all[position]? = some address := by
        have := congrArg (fun xs : List Nat => xs[0]?) suffix
        simpa using this
      have nextSuffix : all.drop (position+1) = addresses := by
        rw [← List.drop_drop, suffix]
        rfl
      have read : extremumItem (.ref collector) position heap = some (.ok (some (.ref address)), heap) := by
        simp [extremumItem, Mutable.sequence, found, List.getElem?_map, index]
      have key := key_result heap (setLocal env "p" (.ref address)) address pair rfl head.2
      by_cases better : score best < score pair
      · obtain ⟨winner, rest, finalFound⟩ := ih (position+1) nextSuffix address pair head.2
        refine ⟨winner, ExtremumReturns.next read key ?_ rest, ?_⟩
        · have cast : (score best : Int) < score pair := by exact_mod_cast better
          simp [SequenceExtremum.choose, HeapCalls.compare, scalarCompare, evalCmpOp,
            num, Mutable.truth, scalarTruth, cast, Except.map]
        · simpa [ProjectEulerStatements.ArgMaximum.select, better] using finalFound
      · obtain ⟨winner, rest, finalFound⟩ := ih (position+1) nextSuffix bestAddress best bestFound
        refine ⟨winner, ExtremumReturns.next read key ?_ rest, ?_⟩
        · have cast : ¬ (score best : Int) < score pair := by exact_mod_cast better
          simp [SequenceExtremum.choose, HeapCalls.compare, scalarCompare, evalCmpOp,
            num, Mutable.truth, scalarTruth, cast, Except.map]
        · simpa [ProjectEulerStatements.ArgMaximum.select, better] using finalFound

private abbrev maximumExpression : Expr := .extremumSequence true (.name "pairs") "p" keyExpression
private def winner (values : List (Int × Int)) : Int × Int := (List.argmax score values).getD (0,0)
private theorem max_result (heap : Mutable.Heap) (env : HeapCalls.Env) (collector : Nat)
    (address : Nat) (addresses : List Nat) (pair : Int × Int) (values : List (Int × Int))
    (getPairs : env "pairs" = some (.ref collector))
    (found : heap[collector]? = some (.list ((address :: addresses).map Mutable.Value.ref)))
    (rows : Rows heap collector (address :: addresses) (pair :: values)) :
    ∃ result,
      Evaluates program env maximumExpression heap (.ref result) heap ∧
      heap[result]? = some (.tuple (pairValues (winner (pair :: values)))) := by
  obtain ⟨head, tail⟩ := List.forall₂_cons.mp rows
  obtain ⟨result, rest, finalFound⟩ := scan_max heap env collector (address::addresses) 1 addresses values
    found rfl tail address pair head.2
  refine ⟨result, ?_, ?_⟩
  · apply Evaluates.extremum_sequence (items := (address::addresses).map Mutable.Value.ref) (Evaluates.lookup getPairs)
      (by simp [Mutable.sequence, found])
    apply ExtremumReturns.next (candidate := .ref address) (score := num (score pair))
      (afterKey := heap) (afterSelection := heap)
    · simp [extremumItem, Mutable.sequence, found]
    · exact key_result heap _ address pair rfl head.2
    · rfl
    · exact rest
  · simpa [winner, ProjectEulerStatements.ArgMaximum.argmax_cons] using finalFound

private abbrev chosenExpression : Expr :=
  .ifExp (.name "pairs") maximumExpression (.tuple [.constant (.int 0), .constant (.int 0)])
private theorem chosen_result (heap : Mutable.Heap) (env : HeapCalls.Env) (collector : Nat)
    (addresses : List Nat) (values : List (Int × Int))
    (getPairs : env "pairs" = some (.ref collector))
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses values) :
    ∃ result finalHeap,
      Evaluates program env chosenExpression heap (.ref result) finalHeap ∧
      finalHeap[result]? = some (.tuple (pairValues (winner values))) := by
  cases rows with
  | nil =>
      refine ⟨heap.length, heap ++ [.tuple (pairValues (0,0))], ?_, ?_⟩
      · apply Evaluates.conditional (flag := false) (Evaluates.lookup getPairs)
          (by simp [Mutable.truth, found])
        exact Evaluates.tuple (.cons Evaluates.constant (.cons Evaluates.constant .nil)) (by simp [pairValues])
      · simp [winner, List.argmax]
  | @cons address pair addresses values head tail =>
      obtain ⟨result, evaluated, contents⟩ := max_result heap env collector address addresses pair values
        getPairs found (.cons head tail)
      refine ⟨result, heap, ?_, contents⟩
      exact Evaluates.conditional (flag := true) (Evaluates.lookup getPairs)
        (by simp [Mutable.truth, found]) evaluated

/-- Mathematical result of the Python reference, including negative range bounds. -/
def reference (a b : Int) : Int := (winner (pairs a b)).1 * (winner (pairs a b)).2
private abbrev naiveArgs : List Arg :=
  [⟨"limit_a", some (.name "int"), none⟩, ⟨"limit_b", some (.name "int"), none⟩]
theorem result (a b : Int) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [num a, num b] heap (num (reference a b)) finalHeap := by
  let env := argumentEnv naiveArgs [num a, num b]
  obtain ⟨middle, addresses, collected, found, rows⟩ := collect_pairs heap env a b rfl rfl
  obtain ⟨address, finalHeap, selected, contents⟩ := chosen_result middle
    (setLocal env "pairs" (.ref heap.length)) heap.length addresses (pairs a b) rfl found rows
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign collected
  apply BlockReturns.unpack (names := ["a", "b"]) (items := pairValues (winner (pairs a b)))
    (afterUnpack := finalHeap) rfl selected
  · simp [Mutable.sequence, contents]
  · rfl
  · apply BlockReturns.return_value
    exact Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl

private theorem interval_map (start : Int) (count : Nat) :
    interval start count = (List.range count).map (fun i : Nat => start + (i : Int)) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [interval, List.range_succ_eq_map, List.map_cons, Int.natCast_zero, add_zero,
        List.map_map, ih]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      omega
private theorem symmetric_interval (a : Nat) :
    interval (-(a : Int)) (2*(a : Int)+1).toNat =
      (List.range (2*a+1)).map (fun i : Nat => (i : Int)-a) := by
  have length : (2*(a : Int)+1).toNat = 2*a+1 := by omega
  rw [length, interval_map]
  apply List.map_congr_left
  intro i _
  omega

theorem reference_eq (a b : Nat) : reference a b = ProjectEulerStatements.P27.naive a b := by
  have fold (as bs : List Int) :
      as.flatMap (fun a => bs.map (a, ·)) = as.foldr (fun a acc => bs.map (a, ·) ++ acc) [] := by
    induction as with
    | nil => rfl
    | cons a as ih => simp only [List.flatMap_cons, List.foldr_cons, ih]
  simp only [reference, pairs, symmetric_interval, fold, winner, ProjectEulerStatements.P27.naive]
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def]
  unfold score
  generalize List.argmax (fun p : Int × Int => consecPrimeLen p.1 p.2) _ = best
  cases best <;> rfl
end ReferenceHeap

/-- Every integer input terminates; nonnegative bounds agree with the existing Euler definition. -/
theorem naive.result (a b : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue program "naive" [.scalar (.int a), .scalar (.int b)] heap
      (.scalar (.int (ProjectEulerStatements.P27.naive a b))) finalHeap := by
  simpa only [ReferenceHeap.reference_eq] using ReferenceHeap.result a b heap

theorem naive.«Returns» (a b : Int) :
    (HeapCalls.scalarFunction program "naive" [.int a, .int b]).Returns := by
  obtain ⟨_, result⟩ := ReferenceHeap.result a b []
  exact result.scalar_returns

theorem naive.«Supported» (a b : Int) :
    (HeapCalls.scalarFunction program "naive" [.int a, .int b]).Supported :=
  (naive.«Returns» a b).supported

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue program "naive_default" [] heap
      (.scalar (.int (ProjectEulerStatements.P27.naive 999 1000))) finalHeap := by
  obtain ⟨finalHeap, result⟩ := naive.result 999 1000 heap
  refine ⟨finalHeap, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.call (.cons HeapCalls.Evaluates.constant (.cons HeapCalls.Evaluates.constant .nil)) result

theorem naive_default.«Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨_, result⟩ := naive_default.result []
  exact result.scalar_returns


theorem naive_default.«Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p27
