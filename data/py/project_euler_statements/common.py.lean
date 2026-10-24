import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«common.py.ast»
import FormalSW
import ProjectEulerStatements.Lib.PositionalDigits
import ProjectEulerStatements.Lib.DivisorEnumeration
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

namespace DivisorsProof

private abbrev encode (items : List Nat) : List Mutable.Value :=
  items.map (fun (value : Nat) => .scalar (.int (value : Int)))
private abbrev test : Expr := .compare (.binOp (.name "n") .mod (.name "d")) [(.eq, .constant (.int 0))]
private abbrev body (address : Nat) : List Stmt :=
  [.ifThen test [.comprehensionAppend address (.name "d")] []]

private theorem loop_result (heap : Mutable.Heap) (n position : Nat) (positive : 0 < position)
    (items : List Nat) (env : HeapCalls.Env) (getN : env "n" = some (.scalar (.int n))) :
    ∃ finalEnv, HeapCalls.BlockContinues program env [.rangeStepLoop "d" position (n + 1) 1 (body heap.length) []]
      (heap ++ [.list (encode items)]) finalEnv
      (heap ++ [.list (encode (items ++ ProjectEulerStatements.DivisorEnumeration.remaining n position))]) := by
  by_cases active : position < n + 1
  · let boundEnv := HeapCalls.setLocal env "d" (.scalar (.int position))
    have savedN : boundEnv "n" = some (.scalar (.int n)) := by simpa [boundEnv, HeapCalls.setLocal] using getN
    have remainder : HeapCalls.Evaluates program boundEnv (.binOp (.name "n") .mod (.name "d"))
        (heap ++ [.list (encode items)]) (.scalar (.int (↑(n % position)))) (heap ++ [.list (encode items)]) :=
      HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup savedN) (HeapCalls.Evaluates.lookup rfl)
        (by simp [Mutable.binary, scalarBinary, positive.ne', positive])
    have tested : HeapCalls.Evaluates program boundEnv test (heap ++ [.list (encode items)])
        (.scalar (.bool (decide (n % position = 0)))) (heap ++ [.list (encode items)]) :=
      HeapCalls.Evaluates.compare remainder HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero])
    let nextItems := if n % position = 0 then items ++ [position] else items
    have step : HeapCalls.BlockContinues program boundEnv (body heap.length)
        (heap ++ [.list (encode items)]) boundEnv (heap ++ [.list (encode nextItems)]) := by
      by_cases divides : n % position = 0
      · apply HeapCalls.BlockContinues.branch (flag := true) (by simpa [divides] using tested) rfl
        have emitted := HeapCalls.BlockContinues.comprehension_append
          (globals := []) (module := program) (env := boundEnv) (address := heap.length)
          (heap := heap ++ [.list (encode items)]) (HeapCalls.Evaluates.lookup (name := "d") rfl)
          (by simp : (heap ++ [.list (encode items)])[heap.length]? = some (.list (encode items)))
        simpa [nextItems, divides, encode, List.map_append] using emitted
      · simpa [body, nextItems, divides] using
          HeapCalls.BlockContinues.branch (yes := [.comprehensionAppend heap.length (.name "d")]) (no := [])
            (flag := false) (by simpa [divides] using tested) rfl HeapCalls.BlockContinues.nil
    obtain ⟨finalEnv, rest⟩ := loop_result heap n (position + 1) (by omega) nextItems boundEnv savedN
    refine ⟨finalEnv, ?_⟩
    rw [ProjectEulerStatements.DivisorEnumeration.remaining_step n position active]
    apply HeapCalls.BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
    by_cases divides : n % position = 0
    all_goals simpa [body, Calls.loopContinuation, Calls.loopControl, nextItems, divides,
      List.append_assoc, Nat.cast_add, Nat.cast_one] using step.append rest
  · refine ⟨env, ?_⟩
    rw [ProjectEulerStatements.DivisorEnumeration.remaining_done n position (by omega)]
    simp only [List.append_nil]
    exact HeapCalls.BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) HeapCalls.BlockContinues.nil
termination_by n + 1 - position
decreasing_by omega

end DivisorsProof

/-- Bounded trial division produces precisely the positive divisors in order. -/
theorem divisors.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "divisors" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [.list ((ProjectEulerStatements.DivisorEnumeration.values n).map
        (fun (value : Nat) => .scalar (.int (value : Int))))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  have tested : HeapCalls.Evaluates program (HeapCalls.argumentEnv [⟨"n", some (.name "int"), none⟩] [.scalar (.int n)])
      (.compare (.name "n") [(.eq, .constant (.int 0))]) heap (.scalar (.bool (decide (n = 0)))) heap :=
    HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases zero : n = 0
  · subst n
    apply HeapCalls.BlockReturns.branch (flag := true) (by simpa using tested) rfl
    exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.list .nil)
  · apply HeapCalls.BlockReturns.branch (flag := false) (by simpa [zero] using tested) rfl
    apply HeapCalls.BlockReturns.return_value
    let env := HeapCalls.comprehensionEnv
      (HeapCalls.argumentEnv [⟨"n", some (.name "int"), none⟩] [.scalar (.int n)])
      [("d", .call (.name "range") [.constant (.int 1), .binOp (.name "n") .add (.constant (.int 1))], [DivisorsProof.test])]
    obtain ⟨finalEnv, loop⟩ := DivisorsProof.loop_result heap n 1 (by decide) [] env rfl
    apply HeapCalls.Evaluates.list_comp_range
      (.cons HeapCalls.Evaluates.constant (.cons
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant rfl) .nil)) rfl
    simpa [ProjectEulerStatements.DivisorEnumeration.remaining_one] using loop

theorem divisors.negative (n : Int) (negative : n < 0) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "divisors" [.scalar (.int n)] heap (.ref heap.length) (heap ++ [.list []]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := heap)
    (HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, show n ≠ 0 by omega])) rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.list_comp_range
    (.cons HeapCalls.Evaluates.constant (.cons
      (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant rfl) .nil)) rfl
  exact HeapCalls.BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) HeapCalls.BlockContinues.nil

theorem divisors.«Returns» (n : Int) :
    (HeapCalls.call program "divisors" [.scalar (.int n)] []).Returns := by
  by_cases nonnegative : 0 ≤ n
  · simpa [Int.toNat_of_nonneg nonnegative] using (divisors.result n.toNat []).returns
  · exact (divisors.negative n (by omega) []).returns

theorem divisors.«Supported» (n : Int) :
    (HeapCalls.call program "divisors" [.scalar (.int n)] []).Supported :=
  (divisors.«Returns» n).supported


/-- Reversing the computed digits allocates a second list and preserves the first. -/
theorem digits_be.result (n base : Nat) (hb : 1 < base) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "digits_be" [.scalar (.int n), .scalar (.int base)] heap
      (.ref (heap.length + 1))
      (heap ++ [.list ((Nat.digits base n).map (fun (d : Nat) => .scalar (.int (d : Int)))),
        .list (((Nat.digits base n).map (fun (d : Nat) => .scalar (.int (d : Int)))).reverse)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  convert HeapCalls.Evaluates.reversed_list
    (items := (Nat.digits base n).map (fun (d : Nat) => .scalar (.int d)))
    (HeapCalls.Evaluates.call
      (env := HeapCalls.argumentEnv ((findFunctionIn program.body "digits_be").getD ([], [])).1
        [.scalar (.int n), .scalar (.int base)])
      (.cons (HeapCalls.Evaluates.lookup (name := "n") rfl)
        (.cons (HeapCalls.Evaluates.lookup (name := "base") rfl) .nil))
      (digits_le.result n base hb heap)) (by simp) using 1 <;>
    simp [List.append_assoc]

namespace OfDigitsProof
open ProjectEulerStatements.PositionalDigits

private abbrev body : List Stmt :=
  [.augAssign (.name "n") .add (.binOp (.name "d") .mult (.name "mul")),
    .augAssign (.name "mul") .mult (.name "base")]

private theorem loop (items remaining : List Int) (heap : Mutable.Heap) (address position : Nat)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n))))
    (suffix : items.drop position = remaining) (env : HeapCalls.Env) (base total multiplier : Int)
    (getBase : env "base" = some (.scalar (.int base)))
    (getTotal : env "n" = some (.scalar (.int total)))
    (getMultiplier : env "mul" = some (.scalar (.int multiplier))) :
    HeapCalls.BlockReturns program env
      [.sequenceStepLoop "d" (.ref address) position body [], .return (.name "n")]
      heap (.scalar (.int (total + multiplier * value base remaining))) heap := by
  have sequence : Mutable.sequence (.ref address) heap =
      some (.ok (items.map fun n => .scalar (.int n)), heap) := by simp [Mutable.sequence, found]
  induction remaining generalizing position env total multiplier with
  | nil =>
      apply HeapCalls.BlockReturns.sequence_done (source := .ref address) sequence
      · have missing : items[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        simp [missing]
      · simpa using HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup getTotal)
  | cons digit rest ih =>
      have item : items[position]? = some digit := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      rw [ProjectEulerStatements.PositionalDigits.step]
      apply HeapCalls.BlockReturns.sequence_step (source := .ref address) (value := .scalar (.int digit)) sequence (by simp [item])
      apply HeapCalls.BlockReturns.augAssign
        (left := .scalar (.int total)) (right := .scalar (.int (digit * multiplier)))
        (value := .scalar (.int (total + digit * multiplier))) (middle := heap) (afterOperation := heap)
      · simpa [HeapCalls.setLocal] using getTotal
      · exact HeapCalls.Evaluates.binary (av := .scalar (.int digit))
          (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal]))
          (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using getMultiplier)) rfl
      · rfl
      apply HeapCalls.BlockReturns.augAssign
        (left := .scalar (.int multiplier)) (right := .scalar (.int base))
        (value := .scalar (.int (multiplier * base))) (middle := heap) (afterOperation := heap)
      · simpa [HeapCalls.setLocal] using getMultiplier
      · exact HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using getBase)
      · rfl
      apply ih
      · simp [List.drop_add_one_eq_tail_drop, suffix]
      · simpa [HeapCalls.setLocal] using getBase
      · simp [HeapCalls.setLocal]
      · simp [HeapCalls.setLocal]

end OfDigitsProof

/-- Positional evaluation terminates for any integer digits and base, including negative bases. -/
theorem of_digits_le.result (items : List Int) (base : Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "of_digits_le" [.ref address, .scalar (.int base)] heap
      (.scalar (.int (ProjectEulerStatements.PositionalDigits.value base items))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.for_sequence (items := items.map fun n => .scalar (.int n))
    (by intros; simp) (HeapCalls.Evaluates.lookup rfl)
    (by simp [Mutable.sequence, found])
  simpa using OfDigitsProof.loop items items heap address 0 found rfl _ base 0 1 rfl rfl rfl

/-- Big-endian evaluation reverses a fresh copy before running the same positional loop. -/
theorem of_digits_be.result (items : List Int) (base : Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (items.map fun n => .scalar (.int n)))) :
    HeapCalls.ReturnsValue program "of_digits_be" [.ref address, .scalar (.int base)] heap
      (.scalar (.int (ProjectEulerStatements.PositionalDigits.value base items.reverse)))
      (heap ++ [.list ((items.map fun n => .scalar (.int n)).reverse)]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.call
    (.cons (HeapCalls.Evaluates.reversed_list (HeapCalls.Evaluates.lookup rfl) found)
      (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
  exact of_digits_le.result items.reverse base _ heap.length (by simp)

end data.«project-euler-statements».data.py.project_euler_statements.common
