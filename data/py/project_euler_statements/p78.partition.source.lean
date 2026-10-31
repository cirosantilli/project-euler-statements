import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p78.py.ast»
import lang.py.FormalSW.MemoCallRules
import ProjectEulerStatements.P76

/-! The original partition helpers execute with a shared exact two-integer memoization cache. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p78
open FormalSW.PyAst MemoCalls
open ProjectEulerStatements.P76 (bounded bounded_zero bounded_no_parts bounded_step)
set_option Elab.async false

abbrev program := P78Ast.module

def cacheSpec (key : Key) (value : Constant) : Prop :=
  ∃ n max : Int, key = ⟨"partition_go", [n, max], none⟩ ∧ value = .int (bounded n max)

theorem cache_unique (n max : Int) (value : Constant)
    (correct : cacheSpec ⟨"partition_go", [n, max], none⟩ value) :
    value = .int (bounded n max) := by
  obtain ⟨otherN, otherMax, same, rfl⟩ := correct
  have equal : n = otherN ∧ max = otherMax := by simpa [Key.mk.injEq] using same
  rcases equal with ⟨rfl, rfl⟩
  rfl

theorem partition_go.result (n max : Int) (nonnegative : 0 ≤ n) (maxNonnegative : 0 ≤ max) :
    ReturnsValue program ["partition_go"] cacheSpec "partition_go" [.int n, .int max]
      (.int (bounded n max)) := by
  induction measure : n.toNat+max.toNat using Nat.strong_induction_on generalizing n max with
  | h size ih =>
      let args := ((findFunctionIn program.body "partition_go").getD ([], [])).1
      let body := ((findFunctionIn program.body "partition_go").getD ([], [])).2
      let entry := argumentEnv args [.int n, .int max]
      have getN : entry "n" = some (.int n) := rfl
      have getMax : entry "max_" = some (.int max) := rfl
      have zeroTest : Evaluates program ["partition_go"] cacheSpec entry
          (.compare (.name "n") [(.eq, .constant (.int 0))]) (.bool (decide (n = 0))) := by
        apply Evaluates.compare (Evaluates.lookup getN) Evaluates.constant
        simp [scalarCompare, evalCmpOp]
      have maxTest : Evaluates program ["partition_go"] cacheSpec entry
          (.compare (.name "max_") [(.eq, .constant (.int 0))]) (.bool (decide (max = 0))) := by
        apply Evaluates.compare (Evaluates.lookup getMax) Evaluates.constant
        simp [scalarCompare, evalCmpOp]
      apply BlockReturns.memoized_function (values := [n, max]) (args := args) (body := body)
        (by simp) rfl rfl
      · by_cases zero : n = 0
        · rw [zero, bounded_zero]
          apply BlockReturns.branch (value := .bool true)
            (by simpa only [entry, zero, decide_true] using zeroTest)
          exact BlockReturns.return_value Evaluates.constant
        · apply BlockReturns.branch (value := .bool false)
            (by simpa only [zero, decide_false] using zeroTest)
          by_cases empty : max = 0
          · rw [empty, bounded_no_parts n 0 (by omega) (by omega)]
            apply BlockReturns.branch (value := .bool true)
              (by simpa only [entry, empty, decide_true] using maxTest)
            exact BlockReturns.return_value Evaluates.constant
          · apply BlockReturns.branch (value := .bool false)
              (by simpa only [empty, decide_false] using maxTest)
            rw [bounded_step n max (by omega) (by omega)]
            have enoughTest : Evaluates program ["partition_go"] cacheSpec entry
                (.compare (.name "max_") [(.ltE, .name "n")]) (.bool (decide (max ≤ n))) :=
              Evaluates.compare (Evaluates.lookup getMax) (Evaluates.lookup getN) rfl
            have rightCall := ih (n.toNat+(max-1).toNat) (by omega) n (max-1)
              nonnegative (by omega) rfl
            have right : Evaluates program ["partition_go"] cacheSpec entry
                (.call (.name "partition_go") [.name "n",
                  .binOp (.name "max_") .sub (.constant (.int 1))])
                (.int (bounded n (max-1))) := by
              apply Evaluates.call _ rightCall
              exact .cons (Evaluates.lookup getN) (.cons
                (Evaluates.binary (Evaluates.lookup getMax) Evaluates.constant rfl) .nil)
            apply BlockReturns.return_value
            by_cases enough : max ≤ n
            · simp only [if_pos enough]
              have leftCall := ih ((n-max).toNat+max.toNat) (by omega) (n-max) max
                (by omega) maxNonnegative rfl
              apply Evaluates.binary (av := .int (bounded (n-max) max))
                (bv := .int (bounded n (max-1)))
              · apply Evaluates.conditional
                  (by simpa only [enough, decide_true] using enoughTest)
                apply Evaluates.call _ leftCall
                exact .cons (Evaluates.binary (Evaluates.lookup getN)
                  (Evaluates.lookup getMax) rfl) (.cons (Evaluates.lookup getMax) .nil)
              · exact right
              · rfl
            · simp only [if_neg enough]
              apply Evaluates.binary (av := .int 0) (bv := .int (bounded n (max-1)))
              · exact Evaluates.conditional
                  (by simpa only [enough, decide_false] using enoughTest) Evaluates.constant
              · exact right
              · rfl
      · exact ⟨n, max, rfl, rfl⟩
      · exact cache_unique n max

theorem partition.result (n : Nat) :
    ReturnsValue program ["partition_go"] cacheSpec "partition" [.int n]
      (.int (ProjectEulerStatements.P76.countWays n n)) := by
  apply BlockReturns.function (by simp) rfl rfl
  apply BlockReturns.return_value
  have called := partition_go.result n n (by omega) (by omega)
  rw [ProjectEulerStatements.P76.bounded_nat] at called
  apply Evaluates.call _ called
  exact .cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)

end data.«project-euler-statements».data.py.project_euler_statements.p78
