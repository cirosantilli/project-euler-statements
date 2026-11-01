import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Orders

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

def integersFor (xs : List Int) : List Int := collectedIntegers (Permutations.rows xs.length xs)
def runLength (xs : List Int) : Nat := ProjectEulerSolutions.PositiveRun.length (integersFor xs)

/-- Python's positional permutation order affects neither expression coverage nor integer membership. -/
theorem mem_integersFor (xs : List Int) (n : Int) :
    n ∈ integersFor xs ↔ 0 < n ∧
      (n : Rat) ∈ ProjectEulerSolutions.ArithmeticExpressions.permuted (xs.map (fun (a : Int) => (a : Rat))) := by
  simp only [integersFor, collectedIntegers, List.mem_flatMap, orderIntegers,
    mem_enumerated_integers, ProjectEulerSolutions.ArithmeticExpressions.permuted]
  constructor
  · rintro ⟨order, member, positive, result⟩
    exact ⟨positive, order.map (fun (a : Int) => (a : Rat)),
      List.mem_permutations.mpr ((Permutations.mem_rows_full_iff.mp member).map _), result⟩
  · rintro ⟨positive, order, member, result⟩
    have pythonOrder := Permutations.mem_rows_full_iff.mpr (List.mem_permutations.mp member)
    rw [List.length_map, Permutations.rows_map] at pythonOrder
    obtain ⟨original, rowMember, rfl⟩ := List.mem_map.mp pythonOrder
    exact ⟨original, rowMember, positive, result⟩

/-- The complete helper returns the run for every integer tuple and preserves all caller objects. -/
theorem result (xs : List Int) (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (xs.map Heap.number))) :
    ∃ extra, ReturnsValue program "consecutive_for_digits" [.ref address] heap
      (Heap.number (runLength xs)) (heap ++ extra) globals := by
  let args := ((findFunctionIn program.body "consecutive_for_digits").getD ([], [])).1
  let source := ((findFunctionIn program.body "consecutive_for_digits").getD ([], [])).2
  let entry := functionEnv args source [.ref address] globals
  let initialized := setLocal entry "integers" (.ref heap.length)
  have getDigits : initialized "digits" = some (.ref address) := by cases globals <;> rfl
  have getOut : initialized "integers" = some (.ref heap.length) := by simp [initialized, setLocal]
  have inputAfter : (working heap [] [])[address]? = some (.tuple (xs.map Heap.number)) :=
    prefix_found heap [.list []] address _ input
  have captured : permutationRows [.ref address, .scalar .none] (working heap [] []) =
      some (.ok (permutationSources (Permutations.rows xs.length xs)), working heap [] []) := by
    simp [permutationRows, Permutations.acquire, Mutable.sequence, inputAfter, Permutations.size,
      Except.map, permutationSources, Permutations.rows_map, List.map_map, Function.comp_def]
  obtain ⟨extra, finalEnv, executed, kept⟩ := orders_loop (Permutations.rows xs.length xs) heap [] []
    initialized globals getOut
  simp only [List.nil_append] at executed
  have traversed : BlockContinues program initialized
      [.forIn (.name "order") (.permutationsIterable [.name "digits", .constant .none]) orderBody []]
      (working heap [] []) finalEnv (working heap ((integersFor xs).map Heap.number) extra) globals :=
    BlockContinues.for_permutations (.cons (Evaluates.lookup getDigits) (.cons Evaluates.constant .nil))
      captured executed
  have counted := consecutive_count.result (integersFor xs)
    (working heap ((integersFor xs).map Heap.number) extra) heap.length globals
    (found heap ((integersFor xs).map Heap.number) extra)
  refine ⟨.list ((integersFor xs).map Heap.number) :: extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply traversed.returns
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup
    ((kept "integers" (by decide) (by decide) (by decide)).trans getOut)) .nil) counted

end data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits
