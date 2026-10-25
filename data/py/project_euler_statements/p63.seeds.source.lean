import data.«project-euler-statements».data.py.project_euler_statements.«p63.digits.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p63.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PowerfulDigits
private abbrev program := P63Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
variable {globals : Mutable.Globals}

def seedCondition : Expr :=
  .compare (.call (.name "num_digits") [.binOp (.name "a") .pow (.name "n"), .name "base"])
    [(.eq, .name "n")]
def seedBody : List Stmt :=
  [.ifThen seedCondition [.augAssign (.name "total") .add (.constant (.int 1))] []]

theorem power_evaluates (seed exponent : Nat) (left right : Expr) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (getLeft : Evaluates program env left heap (number seed) heap globals)
    (getRight : Evaluates program env right heap (number exponent) heap globals) :
    Evaluates program env (.binOp left .pow right) heap (number (seed ^ exponent)) heap globals := by
  apply Evaluates.binary getLeft getRight
  simp [Mutable.binary, scalarBinary, number, show ¬ (exponent : Int) < 0 by omega]

/-- Each seed test uses the source digit-list conversion and increments exactly its indicator. -/
theorem seed_cell (base seed exponent total : Nat) (valid : 2 ≤ base) (inside : seed < base)
    (positive : 1 ≤ exponent) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getBase : env "base" = some (number base)) (getSeed : env "a" = some (number seed))
    (getN : env "n" = some (number exponent)) (getTotal : env "total" = some (number total)) :
    ∃ after : HeapCalls.Env,
      BlockContinues program env seedBody heap after
        (heap ++ [.list ((Nat.digits base (seed ^ exponent)).map number)]) globals ∧
      after "base" = some (number base) ∧ after "n" = some (number exponent) ∧
      after "total" = some (number (total + hit base seed exponent)) := by
  let middle := heap ++ [.list ((Nat.digits base (seed ^ exponent)).map number)]
  have tested : Evaluates program env seedCondition heap
      (flag (decide (width base (seed ^ exponent) = exponent))) middle globals := by
    apply Evaluates.compare (av := number (width base (seed ^ exponent)))
      (bv := number exponent) (middle := middle) (afterRight := middle)
    · exact Evaluates.call
        (.cons (power_evaluates seed exponent _ _ heap env (Evaluates.lookup getSeed) (Evaluates.lookup getN))
          (.cons (Evaluates.lookup getBase) .nil))
        (num_digits.result (seed ^ exponent) base valid heap globals)
    · exact Evaluates.lookup getN
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
  by_cases yes : base ^ (exponent - 1) ≤ seed ^ exponent
  · have qualifies := (power_width_eq base seed exponent valid inside positive).mpr yes
    refine ⟨setLocal env "total" (number (total + 1)), ?_, ?_, ?_, ?_⟩
    · apply BlockContinues.branch (flag := true) (by simpa only [qualifies, decide_true] using tested) rfl
      exact BlockContinues.augAssign getTotal Evaluates.constant
        (by simp [inplace, Mutable.binary, scalarBinary, number, middle])
    · simpa [setLocal] using getBase
    · simpa [setLocal] using getN
    · simp [setLocal, hit, yes]
  · have misses : width base (seed ^ exponent) ≠ exponent := by
      intro equal
      exact yes ((power_width_eq base seed exponent valid inside positive).mp equal)
    refine ⟨env, ?_, getBase, getN, ?_⟩
    · apply BlockContinues.branch (flag := false) (by simpa only [misses, decide_false] using tested) rfl
      exact BlockContinues.nil
    · simpa only [hit, if_neg yes, Nat.add_zero] using getTotal

theorem seed_loop (base exponent first count total : Nat) (valid : 2 ≤ base)
    (positive : 1 ≤ exponent) (endpoint : first + count = base)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getBase : env "base" = some (number base)) (getN : env "n" = some (number exponent))
    (getTotal : env "total" = some (number total)) :
    ∃ after finalHeap,
      BlockContinues program env [.rangeStepLoop "a" first base 1 seedBody []]
        heap after finalHeap globals ∧
      after "base" = some (number base) ∧ after "n" = some (number exponent) ∧
      after "total" = some (number (total + sumWindow (fun seed => hit base seed exponent) first count)) := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨env, heap, ?_, getBase, getN, ?_⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) BlockContinues.nil
      · simpa using getTotal
  | succ count ih =>
      let entered := setLocal env "a" (number first)
      obtain ⟨middle, executed, keptBase, keptN, keptTotal⟩ := seed_cell base first exponent total valid
        (by omega) positive heap entered
        (by simpa [entered, setLocal] using getBase) (by simp [entered, setLocal])
        (by simpa [entered, setLocal] using getN) (by simpa [entered, setLocal] using getTotal)
      obtain ⟨after, finalHeap, rest, finalBase, finalN, finalTotal⟩ :=
        ih (first + 1) (total + hit base first exponent) (by omega) _ middle keptBase keptN keptTotal
      refine ⟨after, finalHeap, ?_, finalBase, finalN, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl seedBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using executed.append rest
      · simpa only [sumWindow_succ, ← Nat.add_assoc] using finalTotal

end data.«project-euler-statements».data.py.project_euler_statements.p63.naive
