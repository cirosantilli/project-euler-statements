import data.«project-euler-statements».data.py.project_euler_statements.«p87.py.lean.d».Loops
import ProjectEulerSolutions.Lib.ListEraseDups
import lang.py.FormalSW.ScalarSetLemmas

namespace data.«project-euler-statements».data.py.project_euler_statements.p87.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PrimePowerTriples
set_option Elab.async false

def setKeys (items : List Nat) : List Constant := items.eraseDups.map (fun (n : Nat) => .int n)

/-- Python's final set removes duplicate representations before its length is observed. -/
theorem count_result (items : List Nat) (base : Mutable.Heap) (env : HeapCalls.Env)
    (getSums : env "sums" = some (.ref base.length)) :
    Evaluates program env (.builtinCall .len [.builtinCall .set [.name "sums"]])
      (working base items) (number items.toFinset.card) (working base items ++ [.set (setKeys items)]) := by
  let heap := working base items
  have found : heap[base.length]? = some (.list ((items.map (fun (n : Nat) => Constant.int n)).map Mutable.Value.scalar)) := by
    simp [heap, working, natValues, number, List.map_map]
  have constructed := Mutable.setFrom_list heap base.length (items.map (fun (n : Nat) => Constant.int n)) found
  rw [ScalarSet.fold_insert_nats] at constructed
  apply Evaluates.builtin (name := .len) (values := [.ref heap.length])
    (middle := heap ++ [.set (setKeys items)])
  · apply Evaluates.Arguments.cons (middle := heap ++ [.set (setKeys items)])
    · apply Evaluates.builtin (name := .set) (values := [.ref base.length]) (middle := heap)
      · exact .cons (Evaluates.lookup getSums) .nil
      · simpa only [primitive, setKeys] using constructed
    · exact .nil
  · simp [primitive, Mutable.length, setKeys, number, ProjectEulerSolutions.ListEraseDups.length_eq_card, heap]

theorem positive_result (limit : Nat) (positive : 0 < limit) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap
      (number (exhaustive limit).card) (heap ++ extra) := by
  let items := primes_below.values (Nat.sqrt limit + 1)
  let base := heap ++ [.list (natValues items)]
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  have setup : BlockContinues program initial (code.take 3) heap (inputEnv initial heap) (working base []) := by
    simpa [inputHeap, base, items, working, natValues, numbers, List.map_map, List.append_assoc] using
      prepare limit positive heap initial rfl
  have ready : Locals (inputEnv initial heap) limit heap.length base.length := by
    constructor
    · rfl
    · rfl
    · simp [inputEnv, base, setLocal]
  obtain ⟨finalEnv, collected, finalReady⟩ := collect limit items base heap.length (by simp [base]) []
    (inputEnv initial heap) ready
  have cardinality : (referenceValues limit items).toFinset.card = (exhaustive limit).card :=
    congrArg Finset.card (referenceValues_complete limit items (primes_below.complete limit))
  refine ⟨[.list (natValues items), .list (natValues (referenceValues limit items)),
    .set (setKeys (referenceValues limit items))], ?_⟩
  apply BlockReturns.function rfl rfl
  apply setup.returns
  apply (show BlockContinues program (inputEnv initial heap) [code[3]'(by decide)]
    (working base []) finalEnv (working base (referenceValues limit items)) from
      by simpa only [List.nil_append] using collected).returns
  apply BlockReturns.return_value
  simpa only [cardinality, base, working, List.append_assoc, List.cons_append, List.nil_append] using
    count_result (referenceValues limit items) base finalEnv finalReady.sums

/-- The entire reference source terminates and returns the exact distinct count for any signed limit. -/
theorem result (limit : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap
      (number (exhaustive limit.toNat).card) (heap ++ extra) := by
  by_cases nonpositive : limit ≤ 0
  · refine ⟨[], ?_⟩
    simpa [empty_nonpositive limit nonpositive] using nonpositive_result limit nonpositive heap
  · lift limit to Nat using (by omega : 0 ≤ limit)
    simpa only [Int.toNat_natCast] using positive_result limit (by omega) heap

end data.«project-euler-statements».data.py.project_euler_statements.p87.naive
