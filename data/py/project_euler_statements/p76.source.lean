import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p76.py.ast»
import lang.py.FormalSW.MemoCallRules
import ProjectEulerStatements.P76

/-! The partition recurrence executes with a shared, exact two-argument memoization cache. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p76
open FormalSW.PyAst FormalSW.PyAst.MemoCalls
open ProjectEulerStatements.P76
  (bounded bounded_zero bounded_negative bounded_no_parts bounded_step)
set_option Elab.async false

abbrev program := P76Ast.module

def cacheSpec (key : Key) (value : Constant) : Prop :=
  ∃ n max : Int, key = ⟨"count_ways", [n, max]⟩ ∧ value = .int (bounded n max)

theorem cache_unique (n max : Int) (value : Constant)
    (correct : cacheSpec ⟨"count_ways", [n, max]⟩ value) : value = .int (bounded n max) := by
  obtain ⟨otherN, otherMax, same, rfl⟩ := correct
  have equal : n = otherN ∧ max = otherMax := by simpa [Key.mk.injEq] using same
  rcases equal with ⟨rfl, rfl⟩
  rfl

theorem count_ways.result (n max : Int) :
    ReturnsValue program ["count_ways"] cacheSpec "count_ways" [.int n, .int max]
      (.int (bounded n max)) := by
  induction measure : n.toNat+max.toNat using Nat.strong_induction_on generalizing n max with
  | h size ih =>
      let args := ((findFunctionIn program.body "count_ways").getD ([], [])).1
      let body := ((findFunctionIn program.body "count_ways").getD ([], [])).2
      let entry := argumentEnv args [.int n, .int max]
      have getN : entry "n" = some (.int n) := rfl
      have getMax : entry "max_" = some (.int max) := rfl
      have zeroTest : Evaluates program ["count_ways"] cacheSpec entry
          (.compare (.name "n") [(.eq, .constant (.int 0))]) (.bool (decide (n = 0))) :=
        Evaluates.compare (Evaluates.lookup getN) Evaluates.constant
          (by simp [scalarCompare, evalCmpOp])
      have negativeTest : Evaluates program ["count_ways"] cacheSpec entry
          (.compare (.name "n") [(.lt, .constant (.int 0))]) (.bool (decide (n < 0))) :=
        Evaluates.compare (Evaluates.lookup getN) Evaluates.constant rfl
      have maxTest : Evaluates program ["count_ways"] cacheSpec entry
          (.compare (.name "max_") [(.ltE, .constant (.int 0))]) (.bool (decide (max ≤ 0))) :=
        Evaluates.compare (Evaluates.lookup getMax) Evaluates.constant rfl
      apply BlockReturns.memoized_function (values := [n, max]) (args := args) (body := body)
        (by simp) rfl rfl
      · by_cases zero : n = 0
        · rw [zero, bounded_zero]
          apply BlockReturns.branch (value := .bool true)
            (by simpa only [entry, zero, decide_true] using zeroTest)
          exact BlockReturns.return_value Evaluates.constant
        · apply BlockReturns.branch (value := .bool false)
            (by simpa only [zero, decide_false] using zeroTest)
          by_cases negative : n < 0
          · rw [bounded_negative n max negative]
            apply BlockReturns.branch (value := .bool true)
              (by simpa only [negative, decide_true] using negativeTest)
            exact BlockReturns.return_value Evaluates.constant
          · apply BlockReturns.branch (value := .bool false)
              (by simpa only [negative, decide_false] using negativeTest)
            by_cases empty : max ≤ 0
            · rw [bounded_no_parts n max (by omega) empty]
              apply BlockReturns.branch (value := .bool true)
                (by simpa only [empty, decide_true] using maxTest)
              exact BlockReturns.return_value Evaluates.constant
            · apply BlockReturns.branch (value := .bool false)
                (by simpa only [empty, decide_false] using maxTest)
              rw [bounded_step n max (by omega) (by omega)]
              have enoughTest : Evaluates program ["count_ways"] cacheSpec entry
                  (.compare (.name "max_") [(.ltE, .name "n")])
                  (.bool (decide (max ≤ n))) :=
                Evaluates.compare (Evaluates.lookup getMax) (Evaluates.lookup getN) rfl
              have rightCall := ih (n.toNat+(max-1).toNat) (by omega) n (max-1) rfl
              have right : Evaluates program ["count_ways"] cacheSpec entry
                  (.call (.name "count_ways") [.name "n",
                    .binOp (.name "max_") .sub (.constant (.int 1))])
                  (.int (bounded n (max-1))) := by
                apply Evaluates.call _ rightCall
                exact .cons (Evaluates.lookup getN) (.cons
                  (Evaluates.binary (Evaluates.lookup getMax) Evaluates.constant rfl) .nil)
              apply BlockReturns.return_value
              by_cases enough : max ≤ n
              · simp only [if_pos enough]
                have leftCall := ih ((n-max).toNat+max.toNat) (by omega) (n-max) max rfl
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

theorem naive.result (n : Int) :
    ReturnsValue program ["count_ways"] cacheSpec "naive" [.int n]
      (.int (ProjectEulerStatements.P76.result n)) := by
  apply BlockReturns.function (by simp) rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call _ (count_ways.result n (n-1))
  exact .cons (Evaluates.lookup rfl) (.cons
    (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)

end data.«project-euler-statements».data.py.project_euler_statements.p76
