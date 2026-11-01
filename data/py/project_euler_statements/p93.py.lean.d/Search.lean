import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Winner

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection consecutive_for_digits
set_option Elab.async false

def operands (bound : Int) : List Int := (List.range (bound + 1).toNat).map (fun (n : Nat) => (n : Int))
def candidates (bound : Int) : List (List Int) := Combinations.rows 4 (operands bound)
def answer (bound : Int) : List Int := ((candidates bound).argmax runLength).getD []

abbrev endpoint : Expr := .binOp (.name "max_digit") .add (.constant (.int 1))
abbrev poolExpression : Expr := .listComp (.name "$formalsw.range.item")
  [("$formalsw.range.item", .call (.name "range") [endpoint], [])]

theorem source_body : executableBody ((findFunctionIn program.body "naive").getD ([], [])).2 =
    [.assign [.name "best_length"] (.unaryOp .uSub (.constant (.int 1))),
     .assign [.name "best_digits"] (.tuple []),
     .forIn (.name "digits") (.combinationsIterable [poolExpression, .constant (.int 4)]) candidateBody [],
     .return (.name "best_digits")] := rfl

/-- The combination pool includes every nonnegative operand through the signed bound. -/
theorem pool_result (bound : Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getBound : env "max_digit" = some (Heap.number bound)) :
    ∃ extra, Evaluates program env poolExpression heap (.ref heap.length)
      (working heap ((operands bound).map Heap.number) extra) globals := by
  have stop : Evaluates program env endpoint heap (Heap.number (bound + 1)) heap globals :=
    Evaluates.binary (Evaluates.lookup getBound) Evaluates.constant (by simp [Mutable.binary, scalarBinary])
  by_cases nonnegative : 0 ≤ bound + 1
  · obtain ⟨extra, collected⟩ := range_map (globals := globals) program "$formalsw.range.item"
      (.name "$formalsw.range.item") (fun n => Heap.number (n : Int))
      (fun heap env n found => ⟨[], by simpa using
        (Evaluates.lookup (module := program) (globals := globals) (heap := heap) found)⟩)
      heap env [endpoint] [Heap.number (bound + 1)] 0 (bound + 1).toNat (.cons stop .nil)
      (by change Except.ok (ε := ExceptionObject) ((0 : Int), bound + 1, (1 : Int)) =
            .ok (0, ((0 + (bound + 1).toNat : Nat) : Int), 1)
          simp [Int.toNat_of_nonneg nonnegative])
    exact ⟨extra, by simpa only [operands, List.map_map, Function.comp_def, List.range_eq_range'] using collected⟩
  · have empty : (bound + 1).toNat = 0 := by omega
    refine ⟨[], ?_⟩
    simp only [operands, empty, List.range_zero, List.map_nil]
    apply Evaluates.list_comp_range (values := [Heap.number (bound + 1)]) (.cons stop .nil) rfl
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil

/-- Complete reference search, with arbitrary signed bounds and caller heaps. -/
theorem result (bound : Int) (heap : Mutable.Heap) (globals : Mutable.Globals) :
    ∃ address extra, ReturnsValue program "naive" [Heap.number bound] heap (.ref address) (heap ++ extra) globals ∧
      (heap ++ extra)[address]? = some (.tuple ((answer bound).map Heap.number)) := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let source := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := functionEnv args source [Heap.number bound] globals
  let scored := setLocal entry "best_length" (Heap.number (-1))
  obtain ⟨emptyAddress, emptyExtra, allocated, foundEmpty⟩ := allocate_tuple [] heap
  have emptyTuple : Evaluates program scored (.tuple []) heap (.ref emptyAddress) (heap ++ emptyExtra) globals := by
    intro anchors stack
    exact .next rfl (.next (by simp [argumentsState, step, HeapCalls.result, run, primitive, allocated]) .refl)
  let initialized := setLocal scored "best_digits" (.ref emptyAddress)
  have initialReady : Ready none (heap ++ emptyExtra) initialized :=
    ⟨by simp [initialized, scored, setLocal, bestScore], emptyAddress,
      by simp [initialized, setLocal], foundEmpty⟩
  have getBound : initialized "max_digit" = some (Heap.number bound) := by cases globals <;> rfl
  obtain ⟨poolExtra, pooled⟩ := pool_result bound (heap ++ emptyExtra) initialized globals getBound
  let afterPool := working (heap ++ emptyExtra) ((operands bound).map Heap.number) poolExtra
  have captured : combinationRows [.ref (heap ++ emptyExtra).length, Heap.number 4] afterPool =
      some (.ok (permutationSources (candidates bound)), afterPool) := by
    have captured := combinationRows_list afterPool (heap ++ emptyExtra).length 4
      ((operands bound).map Heap.number) (found (heap ++ emptyExtra) _ poolExtra)
    simpa only [candidates, permutationSources, Combinations.rows_map, List.map_map, Function.comp_def] using captured
  obtain ⟨searchExtra, finalEnv, searched, finalReady⟩ := candidate_loop (candidates bound) none afterPool
    initialized globals (initialReady.append (.list ((operands bound).map Heap.number) :: poolExtra))
  obtain ⟨address, getBest, foundBest⟩ := finalReady.digits
  have traversed : BlockContinues program initialized
      [.forIn (.name "digits") (.combinationsIterable [poolExpression, .constant (.int 4)]) candidateBody []]
      (heap ++ emptyExtra) finalEnv (afterPool ++ searchExtra) globals :=
    BlockContinues.for_combinations (.cons pooled (.cons Evaluates.constant .nil)) captured searched
  refine ⟨address, emptyExtra ++ (.list ((operands bound).map Heap.number) :: poolExtra) ++ searchExtra, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (Evaluates.unary Evaluates.constant rfl)
    apply BlockReturns.assign emptyTuple
    simpa only [afterPool, working, List.append_assoc] using
      traversed.returns (BlockReturns.return_value (Evaluates.lookup getBest))
  · simpa only [afterPool, working, List.append_assoc, scan_argmax, answer] using foundBest

def Verified (bound : Int) (heap : Mutable.Heap) (globals : Mutable.Globals) : Prop :=
  ∃ address extra, ReturnsValue program "naive" [Heap.number bound] heap (.ref address) (heap ++ extra) globals ∧
    (heap ++ extra)[address]? = some (.tuple ((answer bound).map Heap.number))

/-- Omitted arguments reuse the generalized source proof, without evaluating the default search. -/
theorem default_result (heap : Mutable.Heap) (globals : Mutable.Globals) :
    ∃ address extra, ReturnsValue program "naive" [] heap (.ref address) (heap ++ extra) globals ∧
      (heap ++ extra)[address]? = some (.tuple ((answer 9).map Heap.number)) := by
  obtain ⟨address, extra, returned, found⟩ := result 9 heap globals
  exact ⟨address, extra, returned.with_defaults rfl rfl rfl, found⟩

end data.«project-euler-statements».data.py.project_euler_statements.p93.naive
