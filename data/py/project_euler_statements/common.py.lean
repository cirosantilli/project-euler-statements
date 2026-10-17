import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«common.py.ast»
import FormalSW
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.common
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := CommonAst.module

private def Trial (n r p : Nat) : Prop :=
  ∀ q ∈ Finset.Icc p r, q % 2 = 1 → ¬ q ∣ n

private instance (n r p : Nat) : Decidable (Trial n r p) := by
  unfold Trial
  infer_instance

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

private def loop : List Stmt :=
  (executableBody ((findFunctionIn program.body "is_prime").getD ([], [])).2).drop 5

private theorem loop_result (n r p : Nat) (hp : 0 < p) (odd : p % 2 = 1)
    (env : ScalarEnv) (hn : env "n" = some (.int n)) (hr : env "r" = some (.int r))
    (hep : env "p" = some (.int p)) :
    BlockReturns program env loop (.bool (decide (Trial n r p))) := by
  induction measure : r + 1 - p using Nat.strong_induction_on generalizing p env with
  | h size ih =>
      by_cases hle : p ≤ r
      · apply BlockReturns.while_loop (value := .bool true)
        · exact Evaluates.compare (Evaluates.lookup hep) (Evaluates.lookup hr)
            (by simp [scalarCompare, evalCmpOp, hle])
        · have divides : Evaluates program env
              (.compare (.binOp (.name "n") .mod (.name "p")) [(.eq, .constant (.int 0))])
              (.bool (decide (p ∣ n))) := by
            apply Evaluates.compare (av := .int ↑(n % p)) (bv := .int 0)
            · exact Evaluates.binary (Evaluates.lookup hn) (Evaluates.lookup hep)
                (by simp [scalarBinary, hp.ne', hp])
            · exact Evaluates.constant
            · simp [scalarCompare, evalCmpOp, Int.natCast_dvd_natCast]
          by_cases hdvd : p ∣ n
          · have bad : ¬Trial n r p := fun h => ((trial_step n r p hle odd).mp h).1 hdvd
            simp only [bad, decide_false]
            apply BlockReturns.branch (value := .bool true)
            · simpa [hdvd] using divides
            · exact BlockReturns.return_value Evaluates.constant
          · simp only [trial_step n r p hle odd, hdvd, not_false_eq_true, true_and]
            apply BlockReturns.branch (value := .bool false)
            · simpa [hdvd] using divides
            · apply BlockReturns.augAssign (value := .int ↑(p + 2))
              · exact Evaluates.binary (Evaluates.lookup hep) Evaluates.constant (by simp [scalarBinary])
              · apply ih (r + 1 - (p + 2)) (by omega) (p + 2) (by omega) (by omega)
                all_goals simp [ScalarEnv.set, hn, hr]
      · have good : Trial n r p := by
          intro q hq _
          have := Finset.mem_Icc.mp hq
          omega
        simp only [good, decide_true]
        apply BlockReturns.while_loop (value := .bool false)
        · exact Evaluates.compare (Evaluates.lookup hep) (Evaluates.lookup hr)
            (by simp [scalarCompare, evalCmpOp, hle])
        · exact BlockReturns.return_value Evaluates.constant

private theorem small_result (n : Int) (hn : n < 2) :
    ReturnsValue program "is_prime" [.int n] (.bool false) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (value := .bool true)
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarCompare, evalCmpOp, hn])
  · exact BlockReturns.return_value Evaluates.constant

theorem is_prime.result (n : Nat) :
    ReturnsValue program "is_prime" [.int n] (.bool (decide (Nat.Prime n))) := by
  by_cases hsmall : n < 2
  · have bad : ¬Nat.Prime n := fun h => by have := h.two_le; omega
    simpa [bad] using small_result n (by omega)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (value := .bool false)
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarCompare, evalCmpOp]; omega)
  · by_cases htwo : n = 2
    · subst n
      simp only [Nat.prime_two, decide_true]
      apply BlockReturns.branch (value := .bool true)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
      · exact BlockReturns.return_value Evaluates.constant
    · apply BlockReturns.branch (value := .bool false)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
          (by simp [scalarCompare, evalCmpOp]; omega)
      · have parity : Evaluates program
            (argumentEnv [{ name := "n", annotation := some (.name "int") }] [.int n])
            (.compare (.binOp (.name "n") .mod (.constant (.int 2))) [(.eq, .constant (.int 0))])
            (.bool (decide (n % 2 = 0))) := by
          apply Evaluates.compare (av := .int ↑(n % 2)) (bv := .int 0)
          · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])
          · exact Evaluates.constant
          · simp [scalarCompare, evalCmpOp, Int.ofNat_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
        by_cases heven : n % 2 = 0
        · have bad : ¬Nat.Prime n := fun h => by have := h.eq_two_or_odd; omega
          simp only [bad, decide_false]
          apply BlockReturns.branch (value := .bool true)
          · simpa [heven] using parity
          · exact BlockReturns.return_value Evaluates.constant
        · apply BlockReturns.branch (value := .bool false)
          · simpa [heven] using parity
          · apply BlockReturns.assign (value := .int (Math.isqrt n))
            · apply Evaluates.library_call (.cons (Evaluates.lookup rfl) .nil) rfl
              change some (Math.isqrtCall [.int n]) = _
              simp [Math.isqrtCall]
            · apply BlockReturns.assign Evaluates.constant
              simpa [trial_prime n (by omega) heven] using
                loop_result n (Math.isqrt n) 3 (by decide) (by decide) _ rfl rfl rfl

theorem is_prime.«Returns» (n : Int) : (Calls.function program "is_prime" [.int n]).Returns := by
  by_cases hn : 0 ≤ n
  · simpa [Int.toNat_of_nonneg hn] using (is_prime.result n.toNat).returns
  · exact (small_result n (by omega)).returns


namespace DigitsProof

private def body : List Stmt :=
  [.expr (.call (.attribute (.name "out") "append") [.binOp (.name "n") .mod (.name "base")]),
   .augAssign (.name "n") .floorDiv (.name "base")]

private def loop : List Stmt :=
  [.whileDo (.name "n") body [], .return (.name "out")]

private def encode (digits : List Nat) : List Mutable.Value :=
  digits.map (fun (digit : Nat) => .scalar (.int (digit : Int)))

private theorem loop_result (n base : Nat) (hb : 1 < base)
    (env : Mutable.Env) (prior : Mutable.Heap) (acc : List Mutable.Value)
    (getN : env "n" = some (.scalar (.int n)))
    (getBase : env "base" = some (.scalar (.int base)))
    (getOut : env "out" = some (.ref prior.length)) :
    HeapCalls.BlockReturns program env loop (prior ++ [Mutable.Object.list (acc)]) (.ref prior.length)
      (prior ++ [Mutable.Object.list (acc ++ encode (Nat.digits base n))]) := by
  by_cases zero : n = 0
  · subst n
    simp only [Nat.digits_zero, encode, List.map_nil, List.append_nil]
    apply HeapCalls.BlockReturns.while_loop (flag := false) (HeapCalls.Evaluates.lookup getN)
    · simp [Mutable.truth, scalarTruth]
    · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup getOut)
  · apply HeapCalls.BlockReturns.while_loop (flag := true) (HeapCalls.Evaluates.lookup getN)
    · simp [Mutable.truth, scalarTruth, zero]
    · apply HeapCalls.BlockReturns.discard
      · apply HeapCalls.Evaluates.append (HeapCalls.Evaluates.lookup getOut) (by simp)
          (old := acc) (current := acc) (afterItem := prior ++ [Mutable.Object.list (acc)])
          (value := .scalar (.int ((n % base : Nat) : Int)))
        · apply HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getN) (HeapCalls.Evaluates.lookup getBase)
          simp [Mutable.binary, scalarBinary, show base ≠ 0 by omega, show 0 < base by omega]
        · simp
      · have appendHeap : (prior ++ [Mutable.Object.list (acc)]).set prior.length (Mutable.Object.list (acc ++ [.scalar (.int ((n % base : Nat) : Int))])) =
            prior ++ [Mutable.Object.list (acc ++ [.scalar (.int ((n % base : Nat) : Int))])] := by simp
        rw [appendHeap]
        apply HeapCalls.BlockReturns.augAssign getN (HeapCalls.Evaluates.lookup getBase)
          (value := .scalar (.int ((n / base : Nat) : Int)))
          (afterOperation := prior ++ [Mutable.Object.list (acc ++ [.scalar (.int ((n % base : Nat) : Int))])])
        · simp [HeapCalls.inplace, Mutable.binary, scalarBinary, show base ≠ 0 by omega, show 0 < base by omega]
        · have recurse := loop_result (n / base) base hb
            (HeapCalls.setLocal env "n" (.scalar (.int ((n / base : Nat) : Int)))) prior
            (acc ++ [.scalar (.int ((n % base : Nat) : Int))])
            (by simp [HeapCalls.setLocal])
            (by simpa [HeapCalls.setLocal] using getBase)
            (by simpa [HeapCalls.setLocal] using getOut)
          rw [Nat.digits_eq_cons_digits_div hb zero]
          simpa only [encode, List.map_cons, List.append_assoc, List.singleton_append] using recurse
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) hb

end DigitsProof

/-- Decimal conversion preserves the caller's heap and returns a fresh list;
the same proof works for every integer base greater than one. -/
theorem digits_le.result (n base : Nat) (hb : 1 < base) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "digits_le" [.scalar (.int n), .scalar (.int base)] heap
      (.ref heap.length) (heap ++ [Mutable.Object.list ((Nat.digits base n).map (fun (digit : Nat) => .scalar (.int (digit : Int))))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  by_cases zero : n = 0
  · subst n
    apply HeapCalls.BlockReturns.branch (middle := heap) (flag := true) (value := .scalar (.bool true))
    · apply HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    · simp [Mutable.truth, scalarTruth]
    · simpa only [Nat.digits_zero, List.map_nil] using
        HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.list HeapCalls.Evaluates.Arguments.nil)
  · apply HeapCalls.BlockReturns.branch (middle := heap) (flag := false) (value := .scalar (.bool false))
    · apply HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, zero]
    · simp [Mutable.truth, scalarTruth]
    · apply HeapCalls.BlockReturns.assign (HeapCalls.Evaluates.list HeapCalls.Evaluates.Arguments.nil)
      exact DigitsProof.loop_result n base hb _ heap [] rfl rfl rfl

/-- The ordinary one-argument call uses the source's default decimal base. -/
theorem digits_le.decimal (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "digits_le" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [Mutable.Object.list ((Nat.digits 10 n).map (fun (digit : Nat) => .scalar (.int (digit : Int))))]) :=
  HeapCalls.ReturnsValue.with_defaults rfl rfl rfl (digits_le.result n 10 (by decide) heap)

theorem digits_le.«Returns» (n base : Int)
    (hn : Calls.Condition program (fun key => if key = "n" then some (.int n) else none) CommonAst.requires_digits_le_0)
    (hb : Calls.Condition program (fun key => if key = "base" then some (.int base) else none) CommonAst.requires_digits_le_1) :
    (HeapCalls.call program "digits_le" [.scalar (.int n), .scalar (.int base)] []).Returns := by
  have nn : 0 ≤ n := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hn rfl
  have bb : 2 ≤ base := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hb rfl
  simpa [Int.toNat_of_nonneg nn, Int.toNat_of_nonneg (by omega : 0 ≤ base)] using
    (digits_le.result n.toNat base.toNat (by omega) []).returns

theorem digits_le.«Supported» (n base : Int)
    (hn : Calls.Condition program (fun key => if key = "n" then some (.int n) else none) CommonAst.requires_digits_le_0)
    (hb : Calls.Condition program (fun key => if key = "base" then some (.int base) else none) CommonAst.requires_digits_le_1) :
    (HeapCalls.call program "digits_le" [.scalar (.int n), .scalar (.int base)] []).Supported :=
  (digits_le.«Returns» n base hn hb).supported

end data.«project-euler-statements».data.py.project_euler_statements.common
