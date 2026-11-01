import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».Counting

/-! Complete reference execution: decimal selections followed by unordered pair counting. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
open choose_faces (Row)
open counting (Required)
set_option Elab.async false

def poolExpression : Expr := .listComp (.name "$formalsw.range.item")
  [("$formalsw.range.item", .call (.name "range") [.constant (.int 10)], [])]

theorem pool_result (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals) :
    ∃ extra, Evaluates program env poolExpression heap (.ref heap.length)
      (heap ++ (.list ((List.range 10).map number) :: extra)) globals := by
  obtain ⟨extra, collected⟩ := HeapCollection.range_map (globals := globals)
    program "$formalsw.range.item" (.name "$formalsw.range.item") number
    (fun heap env value found => ⟨[], by simpa using
      (Evaluates.lookup (module := program) (globals := globals) (heap := heap) found)⟩)
    heap env [.constant (.int 10)] [number 10] 0 10
    (.cons Evaluates.constant .nil) rfl
  exact ⟨extra, collected⟩

def Prepared (count : Int) (heap : Mutable.Heap) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∃ (rows : List Row) (address : Nat) (extra : Mutable.Heap), value = .ref address ∧ after = heap ++ extra ∧
    after[address]? = some (.list (rows.map Row.reference)) ∧
    (∀ row ∈ rows, row.Valid after) ∧
    rows.map Row.labels = if count < 0 then [] else choices count.toNat (List.range 10)

/-- The range and combination collector allocate private lists and retain all caller objects. -/
theorem prepare (count : Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getCount : env "face_count" = some (.scalar (.int count))) :
    HeapMemoCalls.EvaluatesRel program counting.spec env
      (.call (.name "choose_faces") [poolExpression, .name "face_count"])
      heap (Prepared count heap) globals := by
  obtain ⟨poolExtra, pool⟩ := pool_result heap env globals
  let added := .list ((List.range 10).map number) :: poolExtra
  let middle := heap ++ added
  have found : middle[heap.length]? = some (.list ((List.range 10).map number)) := by
    simp [middle, added]
  obtain ⟨rows, garbage, model, selected, valid⟩ :=
    choose_faces.signed_result count heap.length (List.range 10) middle globals found
  have liftedPool := HeapMemoCalls.Evaluates.from_heap (HeapCalls.Extends.refl _) counting.cache_disjoint
    pool (expand69.pool.preserves_append heap added)
  have lifted := HeapMemoCalls.ReturnsValue.from_heap (HeapCalls.Extends.refl _) counting.cache_disjoint
    selected (expand69.pool.preserves_append middle (.list (rows.map Row.reference) :: garbage))
  apply HeapMemoCalls.EvaluatesRel.call
    (HeapMemoCalls.ArgumentsRel.fixed (.cons liftedPool (.cons (HeapMemoCalls.Evaluates.lookup getCount) .nil)))
  rintro values after ⟨rfl, rfl⟩
  apply lifted.rel.consequence
  rintro value after ⟨rfl, rfl⟩
  refine ⟨rows, middle.length, added ++ (.list (rows.map Row.reference) :: garbage), rfl, ?_, ?_, valid, model⟩
  · simp only [HeapCollection.working, middle, List.append_assoc]
  · exact HeapCollection.found middle _ garbage

/-- The actual reference returns the mathematical count for every signed face count. -/
theorem result (count : Int) (required : Required) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (valid : required.Valid heap) :
    HeapMemoCalls.ReturnsRel program counting.spec "naive" [.scalar (.int count), .ref required.address] heap
      (fun value after => value = number (answer count (required.pairs.map can_show.Pair.model)) ∧
        ∃ extra, after = heap ++ extra) globals := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let source := ((findFunctionIn program.body "naive").getD ([], [])).2
  let env := functionEnv args source [.scalar (.int count), .ref required.address] globals
  have getCount : env "face_count" = some (.scalar (.int count)) := by cases globals <;> rfl
  have getRequired : env "required_pairs" = some (.ref required.address) := by cases globals <;> rfl
  apply HeapMemoCalls.BlockReturnsRel.function (by simp [program, P90Ast.module]) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.assign (prepare count heap env globals getCount)
  rintro value after ⟨rows, address, extra, rfl, rfl, found, rowsValid, model⟩
  apply HeapMemoCalls.BlockReturnsRel.assign HeapMemoCalls.Evaluates.constant.rel
  rintro value middle ⟨rfl, rfl⟩
  let bound := setLocal (setLocal env "cubes" (.ref address)) "pairs" (number 0)
  have counted := counting.result required rows address 0 (heap ++ extra) bound globals
    (valid.append extra) rowsValid found (by simp [bound, setLocal])
    (by simpa [bound, setLocal] using getRequired) (by simp [bound, setLocal])
  apply counted.consequence
  rintro value after ⟨same, more, shape⟩
  refine ⟨?_, extra ++ more, by simpa only [List.append_assoc] using shape⟩
  have countModel : countPairs (counting.test required) rows = answer count (required.pairs.map can_show.Pair.model) := by
    change countPairs (fun a b => displays a.labels b.labels (required.pairs.map can_show.Pair.model)) rows = _
    rw [← countPairs_map (fun a b => displays a b (required.pairs.map can_show.Pair.model)) Row.labels rows, model]
    by_cases negative : count < 0 <;> simp [answer, negative, countPairs, referenceCount]
  simpa only [Nat.zero_add, countModel] using same

end data.«project-euler-statements».data.py.project_euler_statements.p90.naive
