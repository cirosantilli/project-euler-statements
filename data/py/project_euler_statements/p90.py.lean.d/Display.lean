import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».Rotation
import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».DisplayCore

/-! Reference display execution composes two private expansions with the lazy requirement scan. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.can_show
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
set_option Elab.async false

private theorem cache_disjoint : HeapMemoCalls.CacheDisjoint program program := by
  intro name cached
  change name ∈ ([] : List String) at cached
  simp at cached

private theorem expand_call (labels : List Nat) (address : Nat) (name : String)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (labels.map number)))
    (getInput : env name = some (.ref address)) :
    HeapMemoCalls.EvaluatesRel program expand69.pool.spec env (.call (.name "expand69") [.name name])
      heap (expand69.Post heap labels) globals := by
  apply HeapMemoCalls.EvaluatesRel.call
    (HeapMemoCalls.ArgumentsRel.fixed (.cons (HeapMemoCalls.Evaluates.lookup getInput) .nil))
  rintro values middle ⟨rfl, rfl⟩
  exact expand69.result labels _ address found globals

def Copies (heap : Mutable.Heap) (a b : List Nat) (values : List Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∃ aa bb extra, values = [.ref aa, .ref bb] ∧ after = heap ++ extra ∧
    after[aa]? = some (.list ((rotated a).map number)) ∧ after[bb]? = some (.list ((rotated b).map number))

/-- Both calls read their original inputs, even when the inputs share an address. -/
theorem copies (a b : List Nat) (addressA addressB : Nat) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (foundA : heap[addressA]? = some (.list (a.map number)))
    (foundB : heap[addressB]? = some (.list (b.map number)))
    (getA : env "a" = some (.ref addressA)) (getB : env "b" = some (.ref addressB)) :
    HeapMemoCalls.ArgumentsRel program expand69.pool.spec env
      [.call (.name "expand69") [.name "a"], .call (.name "expand69") [.name "b"]]
      heap (Copies heap a b) globals := by
  apply HeapMemoCalls.ArgumentsRel.cons (expand_call a addressA "a" heap env globals foundA getA)
  rintro value middle ⟨rfl, garbageA, rfl⟩
  have keptB := HeapCollection.prefix_found heap (.list ((rotated a).map number) :: garbageA) addressB _ foundB
  apply HeapMemoCalls.ArgumentsRel.cons (expand_call b addressB "b" _ env globals keptB getB)
  rintro value after ⟨rfl, garbageB, rfl⟩
  apply HeapMemoCalls.ArgumentsRel.nil
  refine ⟨heap.length, (working heap (rotated a) garbageA).length,
    (.list ((rotated a).map number) :: garbageA) ++ (.list ((rotated b).map number) :: garbageB), rfl, ?_, ?_, ?_⟩
  · simp only [working, HeapCollection.working, List.append_assoc]
  · exact HeapCollection.prefix_found (working heap (rotated a) garbageA)
      (.list ((rotated b).map number) :: garbageB) heap.length _ (HeapCollection.found heap _ garbageA)
  · exact HeapCollection.found _ _ garbageB

def Prepared (heap : Mutable.Heap) (a b : List Nat) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∃ aa bb address extra, value = .ref address ∧ after = heap ++ extra ∧
    after[address]? = some (.tuple [.ref aa, .ref bb]) ∧
    after[aa]? = some (.list ((rotated a).map number)) ∧ after[bb]? = some (.list ((rotated b).map number))

/-- The unpacking wrapper contains the two completed results in Python's evaluation order. -/
theorem prepare (a b : List Nat) (addressA addressB : Nat) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (foundA : heap[addressA]? = some (.list (a.map number)))
    (foundB : heap[addressB]? = some (.list (b.map number)))
    (getA : env "a" = some (.ref addressA)) (getB : env "b" = some (.ref addressB)) :
    HeapMemoCalls.EvaluatesRel program expand69.pool.spec env
      (.tuple [.call (.name "expand69") [.name "a"], .call (.name "expand69") [.name "b"]])
      heap (Prepared heap a b) globals := by
  apply HeapMemoCalls.EvaluatesRel.tuple (copies a b addressA addressB heap env globals foundA foundB getA getB)
  rintro values after ⟨aa, bb, extra, rfl, shape, foundAA, foundBB⟩
  refine ⟨by simp, expand69.pool.preserves_append _ _, aa, bb, after.length,
    extra ++ [.tuple [.ref aa, .ref bb]], rfl, ?_, by simp, ?_, ?_⟩
  · simp only [shape, List.append_assoc]
  · exact HeapCollection.prefix_found after _ aa _ foundAA
  · exact HeapCollection.prefix_found after _ bb _ foundBB

/-- The Python predicate equals the membership model for arbitrary finite requirements and preserves its caller's objects. -/
theorem result (a b : List Nat) (addressA addressB address : Nat) (pairs : List Pair)
    (heap : Mutable.Heap) (globals : Mutable.Globals := [])
    (foundA : heap[addressA]? = some (.list (a.map number)))
    (foundB : heap[addressB]? = some (.list (b.map number)))
    (found : heap[address]? = some (.list (pairs.map Pair.reference)))
    (valid : ∀ pair ∈ pairs, pair.Valid heap) :
    HeapMemoCalls.ReturnsRel program expand69.pool.spec "can_show" [.ref addressA, .ref addressB, .ref address] heap
      (fun value after => value = .scalar (.bool (displays a b (pairs.map Pair.model))) ∧ ∃ extra, after = heap ++ extra)
      globals := by
  let args := ((findFunctionIn program.body "can_show").getD ([], [])).1
  let source := ((findFunctionIn program.body "can_show").getD ([], [])).2
  let env := functionEnv args source [.ref addressA, .ref addressB, .ref address] globals
  have getA : env "a" = some (.ref addressA) := by cases globals <;> rfl
  have getB : env "b" = some (.ref addressB) := by cases globals <;> rfl
  have getPairs : env "required_pairs" = some (.ref address) := by cases globals <;> rfl
  apply HeapMemoCalls.BlockReturnsRel.function (by simp [program, P90Ast.module]) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.unpack_rel (names := ["aa", "bb"]) rfl
    (prepare a b addressA addressB heap env globals foundA foundB getA getB)
  rintro value after ⟨aa, bb, tupleAddress, extra, rfl, shape, tupleFound, foundAA, foundBB⟩
  refine ⟨[.ref aa, .ref bb], after, ?_, rfl, (by intro cache holds; exact holds), ?_⟩
  · simp [Mutable.sequence, tupleFound]
  · let bound := assignNames env ["aa", "bb"] [.ref aa, .ref bb]
    have required : after[address]? = some (.list (pairs.map Pair.reference)) := by
      rw [shape]
      exact HeapCollection.prefix_found heap extra address _ found
    have requiredValid : ∀ pair ∈ pairs, pair.Valid after := by
      intro pair mem
      rw [Pair.Valid, shape]
      exact HeapCollection.prefix_found heap extra pair.address _ (valid pair mem)
    have checked := generator (rotated a) (rotated b) aa bb address pairs after bound globals
      foundAA foundBB required requiredValid (by simp [bound, assignNames, setLocal])
      (by simp [bound, assignNames, setLocal]) (by simpa [bound, assignNames, setLocal] using getPairs)
    have lifted := HeapMemoCalls.Evaluates.from_heap (HeapCalls.Extends.refl _) cache_disjoint checked
      (spec := expand69.pool.spec) (by intro cache holds; exact holds)
    apply HeapMemoCalls.BlockReturnsRel.return_value
    apply lifted.rel.consequence
    rintro value final ⟨rfl, rfl⟩
    refine ⟨?_, extra, shape⟩
    simp only [displays, List.all_map]
    rfl

end data.«project-euler-statements».data.py.project_euler_statements.p90.can_show
