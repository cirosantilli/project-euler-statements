import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p65.py.ast»
import ProjectEulerSolutions.Lib.EConvergentCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p65
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.EConvergents ProjectEulerSolutions.EConvergentCalls
set_option Elab.async false
private abbrev program := P65Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (values : List Nat) := values.map number
variable {globals : Mutable.Globals}

theorem coeff_e.result (k : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "coeff_e" [number k] heap (number (coefficient k)) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact coefficient_expression program k heap _ (by cases globals <;> rfl)

private def collectBody (address : Nat) : List Stmt :=
  [.comprehensionAppend address (.call (.name "coeff_e") [.name "k"])]

private theorem collect_loop (n first count : Nat) (endpoint : first + count = n)
    (heap : Mutable.Heap) (before : List Nat) (env : HeapCalls.Env) :
    ∃ after, BlockContinues program env [.rangeStepLoop "k" first n 1 (collectBody heap.length) []]
      (heap ++ [.list (numbers before)]) after
      (heap ++ [.list (numbers (before ++ (List.range' first count).map coefficient))]) globals := by
  induction count generalizing first before env with
  | zero =>
      refine ⟨env, ?_⟩
      simpa only [List.range'_zero, List.map_nil, List.append_nil] using
        (BlockContinues.range_done (module := program) (env := env)
          (heap := heap ++ [.list (numbers before)]) (body := collectBody heap.length)
          (name := "k") (next := (first : Int)) (stop := n) (stride := 1) (otherwise := [])
          (by simp [Calls.rangeContinues]; omega) BlockContinues.nil)
  | succ count ih =>
      let entered := setLocal env "k" (number first)
      have evaluated : Evaluates program entered (.call (.name "coeff_e") [.name "k"])
          (heap ++ [.list (numbers before)]) (number (coefficient first)) (heap ++ [.list (numbers before)]) globals :=
        Evaluates.call (.cons (Evaluates.lookup (by simp [entered, setLocal])) .nil)
          (coeff_e.result first _ globals)
      have emitted : BlockContinues program entered (collectBody heap.length)
          (heap ++ [.list (numbers before)]) entered
          (heap ++ [.list (numbers (before ++ [coefficient first]))]) globals := by
        simpa [numbers] using BlockContinues.comprehension_append (address := heap.length) evaluated
          (by simp : (heap ++ [.list (numbers before)])[heap.length]? = some (.list (numbers before)))
      obtain ⟨after, rest⟩ := ih (first + 1) (by omega) (before ++ [coefficient first]) entered
      refine ⟨after, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [Calls.loopContinuation, show Calls.loopControl (collectBody heap.length) = false from rfl,
        Bool.false_eq_true, if_false, List.range'_succ, List.map_cons, List.append_assoc,
        List.singleton_append, Int.natCast_add, Int.natCast_one] using emitted.append rest

/-- The reference comprehension allocates exactly its complete coefficient list. -/
theorem coeffs.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "coeffs" [number n] heap (.ref heap.length)
      (heap ++ [.list (numbers (coefficients n))]) globals := by
  let args := ((findFunctionIn program.body "coeffs").getD ([], [])).1
  let body := ((findFunctionIn program.body "coeffs").getD ([], [])).2
  let env := functionEnv args body [number n] globals
  obtain ⟨after, executed⟩ := collect_loop (globals := globals) n 0 n (by omega) heap []
    (comprehensionEnv env [("k", .call (.name "range") [.name "n"], [])])
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.list_comp_range (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) rfl
  simpa only [collectBody, comprehensionFilters, comprehensionBody, numbers, List.map_nil,
    List.nil_append, coefficients, ProjectEulerStatements.P65.coeffs, List.range_eq_range', Nat.zero_add] using executed

end data.«project-euler-statements».data.py.project_euler_statements.p65
