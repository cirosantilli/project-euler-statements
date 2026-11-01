import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».RotationPool

/-! Complete source execution of the reference's list-based 6/9 expansion. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.expand69
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
set_option Elab.async false

private theorem cache_disjoint : HeapMemoCalls.CacheDisjoint program program := by
  intro name cached
  change name ∈ ([] : List String) at cached
  simp at cached

/-- The pooled iterable is evaluated once; the ordinary loop mutates only the fresh output list. -/
theorem loop (base : Mutable.Heap) (labels : List Nat) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getOut : env "out" = some (.ref base.length)) :
    HeapMemoCalls.BlockReturnsRel program pool.spec env
      [.forIn (.name "d") pool.expression loopCode [], .return (.name "out")]
      (working base labels [])
      (fun value after => value = .ref base.length ∧
        ∃ garbage, after = working base (addLabel (addLabel labels 6) 9) garbage) globals := by
  intro anchors stack
  apply HeapMemoCalls.RunsRel.next
    (current := ⟨.block [.forIn (.name "d") pool.expression loopCode [], .return (.name "out")] env,
      stack, working base labels []⟩)
    (following := ⟨.expr pool.expression env,
      .sequence "d" loopCode [] [.return (.name "out")] env :: stack, working base labels []⟩)
    (by trivial) (by rw [pool.expression_eq]; rfl)
  apply (pool.evaluate env (working base labels []) globals anchors
    (.sequence "d" loopCode [] [.return (.name "out")] env :: stack)).bind
  rintro final ⟨value, after, rfl, garbage, shape, address, rfl, found⟩
  have shape' : after = working base labels garbage := by
    simpa only [working, HeapCollection.append, List.nil_append] using shape
  clear shape
  subst after
  have sequence : Mutable.sequence (.ref address) (working base labels garbage) =
      some (.ok [number 6, number 9], working base labels garbage) := by
    simp [Mutable.sequence, found]
  apply HeapMemoCalls.RunsRel.next
    (current := ⟨.value (.ref address), .sequence "d" loopCode [] [.return (.name "out")] env :: stack,
      working base labels garbage⟩)
    (following := ⟨.block [.sequenceStepLoop "d" (.ref address) 0 loopCode [], .return (.name "out")] env,
      stack, working base labels garbage⟩)
    (by trivial) (by simp [HeapCalls.step, HeapCalls.run, sequence, HeapCalls.sequenceSource])
  have plain := (two_steps base labels garbage address found env globals getOut).returns
    (BlockReturns.return_value (rest := []) (Evaluates.lookup (name := "out") (by simpa [afterTwo, setLocal] using getOut)))
  intro callers cache valid
  refine ⟨⟨.value (.ref base.length), stack, working base (addLabel (addLabel labels 6) 9) garbage⟩,
    cache, ?_, pool.preserves_output base labels _ garbage cache valid, ?_⟩
  · exact ⟨_, _, rfl, rfl, garbage, rfl⟩
  · exact HeapMemoCalls.Reaches.from_heap (HeapCalls.Extends.refl _) cache_disjoint (plain anchors stack)

def Post (heap : Mutable.Heap) (labels : List Nat) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  value = .ref heap.length ∧ ∃ garbage, after = working heap (rotated labels) garbage

/-- The returned list is a fresh copy with rotation labels added; all caller objects retain their contents. -/
theorem result (labels : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (labels.map number))) (globals : Mutable.Globals := []) :
    HeapMemoCalls.ReturnsRel program pool.spec "expand69" [.ref address] heap (Post heap labels) globals := by
  let args := ((findFunctionIn program.body "expand69").getD ([], [])).1
  let source := ((findFunctionIn program.body "expand69").getD ([], [])).2
  let env := functionEnv args source [.ref address] globals
  let copiedEnv := setLocal env "out" (.ref heap.length)
  have copy : Evaluates program env (.builtinCall .list [.name "xs"]) heap (.ref heap.length)
      (working heap labels []) globals :=
    Evaluates.builtin (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
      (primitive_list_list heap address (labels.map number) found)
  have liftedCopy := HeapMemoCalls.Evaluates.from_heap (HeapCalls.Extends.refl _) cache_disjoint copy
    (pool.preserves_append heap [.list (labels.map number)])
  have tested := HeapMemoCalls.Evaluates.from_heap (HeapCalls.Extends.refl _) cache_disjoint
    (condition heap labels copiedEnv globals rfl) (spec := pool.spec) (by intro cache valid; exact valid)
  apply HeapMemoCalls.BlockReturnsRel.function (by simp [program, P90Ast.module]) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.assign liftedCopy.rel
  rintro value middle ⟨rfl, rfl⟩
  apply HeapMemoCalls.BlockReturnsRel.branch tested.rel
  rintro value middle ⟨rfl, rfl⟩
  refine ⟨decide (6 ∈ labels ∨ 9 ∈ labels), rfl, ?_⟩
  by_cases active : 6 ∈ labels ∨ 9 ∈ labels
  · simp only [active, decide_true, ↓reduceIte]
    apply (loop heap labels copiedEnv globals rfl).consequence
    rintro value after ⟨same, garbage, shape⟩
    exact ⟨same, garbage, by simpa only [rotated, active, ↓reduceIte] using shape⟩
  · simp only [active, decide_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    apply HeapMemoCalls.BlockReturnsRel.return_value
    apply (HeapMemoCalls.Evaluates.lookup (show copiedEnv "out" = some (.ref heap.length) from rfl)).rel.consequence
    rintro value after ⟨rfl, rfl⟩
    exact ⟨rfl, [], by simp only [rotated, active, ↓reduceIte]⟩

end data.«project-euler-statements».data.py.project_euler_statements.p90.expand69
