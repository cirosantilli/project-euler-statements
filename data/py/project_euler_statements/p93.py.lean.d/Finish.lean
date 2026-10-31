import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Allocation

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
set_option Elab.async false

abbrev positiveTest : Expr := .compare nb [(.gt, .constant (.int 0))]
abbrev negativeTest : Expr := .compare nb [(.lt, .constant (.int 0))]
abbrev appendExpr (expression : Expr) : Stmt := .expr (.call (.attribute (.name "out") "append") [expression])
def finish : List Stmt :=
  [.ifThen positiveTest [appendExpr positiveExpr] [.ifThen negativeTest [appendExpr negativeExpr] []],
   .return (.name "out")]

theorem finish_source :
    (executableBody ((findFunctionIn program.body "eval_ops").getD ([], [])).2).drop 4 = finish := rfl

variable {env : HeapCalls.Env} {heap : Mutable.Heap} {globals : Mutable.Globals}

theorem positive_test (a b : Pair) (ready : Ready env a b) :
    Evaluates program env positiveTest heap (.scalar (.bool (decide (0 < b.1)))) heap globals :=
  Evaluates.compare (Evaluates.lookup ready.numeratorB) Evaluates.constant
    (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])

theorem negative_test (a b : Pair) (ready : Ready env a b) :
    Evaluates program env negativeTest heap (.scalar (.bool (decide (b.1 < 0)))) heap globals :=
  Evaluates.compare (Evaluates.lookup ready.numeratorB) Evaluates.constant
    (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])

/-- Both denominator signs and the skipped zero divisor follow the actual source branches. -/
theorem finish_result (base : Mutable.Heap) (a b : Pair) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (ready : Ready env a b) (out : env "out" = some (.ref (listAddress base))) :
    ∃ extra, BlockReturns program env finish (initialHeap base a b) (.ref (listAddress base)) (base ++ extra) globals ∧
      Heap.ListFound (base ++ extra) (listAddress base) (reference a b) := by
  by_cases positive : 0 < b.1
  · let pair : Pair := (a.1*b.2, a.2*b.1)
    refine ⟨firstObjects a b ++ [.list (firstRefs base ++ [.ref (base.length+4)]), object pair], ?_, ?_⟩
    · apply BlockReturns.branch (flag := true)
        (by simpa only [positive, decide_true] using positive_test (heap := initialHeap base a b) a b ready) rfl
      exact append_pair a b pair base env globals positiveExpr out (positive_pair a b ready)
    · simpa [reference, quotient, positive, positive.ne', pair] using extended_found base a b pair
  · by_cases negative : b.1 < 0
    · let pair : Pair := (-a.1*b.2, -a.2*b.1)
      refine ⟨firstObjects a b ++ [.list (firstRefs base ++ [.ref (base.length+4)]), object pair], ?_, ?_⟩
      · apply BlockReturns.branch (flag := false)
          (by simpa only [positive, decide_false] using positive_test (heap := initialHeap base a b) a b ready) rfl
        apply BlockReturns.branch (flag := true)
          (by simpa only [negative, decide_true] using negative_test (heap := initialHeap base a b) a b ready) rfl
        exact append_pair a b pair base env globals negativeExpr out (negative_pair a b ready)
      · simpa [reference, quotient, positive, negative.ne, pair] using extended_found base a b pair
    · have zero : b.1 = 0 := by omega
      refine ⟨firstObjects a b ++ [.list (firstRefs base)], ?_, ?_⟩
      · apply BlockReturns.branch (flag := false)
          (by simpa only [positive, decide_false] using positive_test (heap := initialHeap base a b) a b ready) rfl
        apply BlockReturns.branch (flag := false)
          (by simpa only [negative, decide_false] using negative_test (heap := initialHeap base a b) a b ready) rfl
        exact BlockReturns.return_value (Evaluates.lookup out)
      · simpa [reference, zero] using initial_found base a b

end data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
