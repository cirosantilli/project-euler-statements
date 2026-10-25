import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p57.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapMemoCalls
import lang.py.FormalSW.HeapMemoCallRules
import lang.py.FormalSW.HeapMemoStarCalls
import ProjectEulerSolutions.Lib.SqrtConvergents
import ProjectEulerSolutions.Lib.HeapCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p57
open FormalSW.PyAst
open ProjectEulerSolutions
set_option Elab.async false

abbrev program := P57Ast.module
abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
def pairValues (p q : Int) : List Mutable.Value := [number p, number q]

def HasPair (heap : Mutable.Heap) (value : Mutable.Value) (p q : Int) : Prop :=
  ∃ address, value = .ref address ∧ heap[address]? = some (.tuple (pairValues p q))

theorem HasPair.append (found : HasPair heap value p q) (extra : Mutable.Heap) :
    HasPair (heap ++ extra) value p q := by
  obtain ⟨address, rfl, found⟩ := found
  exact ⟨address, rfl, HeapCollection.prefix_found heap extra address _ found⟩

def nativePair (heap : Mutable.Heap) (value : Mutable.Value) (n : Nat) : Prop :=
  HasPair heap value (SqrtConvergents.convergent n).1 (SqrtConvergents.convergent n).2

/-- The compiler pool identity is read from the current parsed source, never copied as a hash literal. -/
def baseExpression : Expr :=
  match executableBody ((findFunctionIn program.body "convergent").getD ([], [])).2 with
  | .ifThen _ (.return expression :: _) _ :: _ => expression
  | _ => .constant .none

def baseIdentity : String := (HeapMemoCalls.pooledIdentity baseExpression).getD ""
def baseKey : HeapMemoCalls.Key := HeapMemoCalls.literalKey baseIdentity

theorem baseExpression_eq : baseExpression = HeapMemoCalls.pooledTuple baseIdentity
    [.constant (.int 3), .constant (.int 2)] := rfl

/-- Cached function results and the compiler's shared base tuple coexist without conflating their keys. -/
def spec (heap : Mutable.Heap) (key : HeapMemoCalls.Key) (value : Mutable.Value) : Prop :=
  (∃ n : Nat, key = ⟨"convergent", [(n : Int)]⟩ ∧ nativePair heap value n) ∨
    (key = baseKey ∧ HasPair heap value 3 2)

private theorem convergent_key_ne_base (n : Nat) :
    (⟨"convergent", [(n : Int)]⟩ : HeapMemoCalls.Key) ≠ baseKey := by
  intro same
  have arguments := congrArg MemoCalls.Key.arguments same
  change [(n : Int)] = [] at arguments
  simp at arguments

theorem spec_convergent (heap : Mutable.Heap) (n : Nat) (value : Mutable.Value) :
    spec heap ⟨"convergent", [(n : Int)]⟩ value ↔ nativePair heap value n := by
  constructor
  · rintro (⟨index, same, pair⟩ | ⟨same, _⟩)
    · have arguments := congrArg MemoCalls.Key.arguments same
      have castEqual : (n : Int) = (index : Int) := by simpa using arguments
      have equal : index = n := by omega
      subst index
      exact pair
    · exact False.elim (convergent_key_ne_base n same)
  · intro pair
    exact Or.inl ⟨n, rfl, pair⟩

theorem spec_base (heap : Mutable.Heap) (value : Mutable.Value) :
    spec heap baseKey value ↔ HasPair heap value 3 2 := by
  constructor
  · rintro (⟨index, same, _⟩ | ⟨_, pair⟩)
    · exact False.elim (convergent_key_ne_base index same.symm)
    · exact pair
  · intro pair
    exact Or.inr ⟨rfl, pair⟩

def PairPost (heap : Mutable.Heap) (n : Nat) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∃ extra, after = heap ++ extra ∧ nativePair after value n

theorem spec_preserves_append (heap extra : Mutable.Heap) :
    HeapMemoCalls.Cache.Preserves spec heap (heap ++ extra) := by
  apply HeapMemoCalls.Cache.preserves_append
  rintro key value (⟨n, rfl, found⟩ | ⟨same, found⟩)
  · exact Or.inl ⟨n, rfl, HasPair.append found extra⟩
  · exact Or.inr ⟨same, HasPair.append found extra⟩

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  have extension : Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module := by
    apply Calls.Extends.prepend
    · intro name member
      change name ∈ ["next_frac", "convergent", "naive"] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · intro name member
      change name ∈ ([] : List String) at member
      simp at member
  exact ⟨extension.functions, extension.libraries⟩

/-- The ordinary helper constructs the actual next numerator/denominator tuple. -/
theorem next_frac.ordinary (p q : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapCalls.ReturnsValue program "next_frac" [number p, number q] heap (.ref heap.length)
      (heap ++ [.tuple (pairValues (p+2*q) (p+q))]) globals := by
  let args := ((findFunctionIn program.body "next_frac").getD ([], [])).1
  let body := ((findFunctionIn program.body "next_frac").getD ([], [])).2
  let env := HeapCalls.functionEnv args body [number p, number q] globals
  have getP : env "p" = some (number p) := by cases globals <;> rfl
  have getQ : env "q" = some (number q) := by cases globals <;> rfl
  have twice : HeapCalls.Evaluates program env
      (.binOp (.constant (.int 2)) .mult (.name "q")) heap (number (2*q)) heap globals :=
    HeapCalls.Evaluates.binary HeapCalls.Evaluates.constant (HeapCalls.Evaluates.lookup getQ) rfl
  have numerator : HeapCalls.Evaluates program env
      (.binOp (.name "p") .add (.binOp (.constant (.int 2)) .mult (.name "q")))
      heap (number (p+2*q)) heap globals :=
    HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getP) twice rfl
  have denominator : HeapCalls.Evaluates program env
      (.binOp (.name "p") .add (.name "q")) heap (number (p+q)) heap globals :=
    HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getP) (HeapCalls.Evaluates.lookup getQ) rfl
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.tuple (.cons numerator (.cons denominator .nil)) (by simp [pairValues])

end data.«project-euler-statements».data.py.project_euler_statements.p57

namespace data.«project-euler-statements».data.py.project_euler_statements.p57
open FormalSW.PyAst
open ProjectEulerSolutions
set_option Elab.async false

private abbrev convergentNatural (value : Nat) : Mutable.Value := .scalar (.int (value : Int))

/-- The uncached arithmetic helper executes in the same heap-cache machine without entering the cache. -/
theorem next_frac.heapMemo_result (p q : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapMemoCalls.ReturnsValue program spec "next_frac" [number p, number q] heap (.ref heap.length)
      (heap ++ [.tuple (pairValues (p+2*q) (p+q))]) globals := by
  let args := ((findFunctionIn program.body "next_frac").getD ([], [])).1
  let body := ((findFunctionIn program.body "next_frac").getD ([], [])).2
  let env := HeapCalls.functionEnv args body [number p, number q] globals
  have getP : env "p" = some (number p) := by cases globals <;> rfl
  have getQ : env "q" = some (number q) := by cases globals <;> rfl
  have twice : HeapMemoCalls.Evaluates program spec env
      (.binOp (.constant (.int 2)) .mult (.name "q")) heap (number (2*q)) heap globals :=
    HeapMemoCalls.Evaluates.binary HeapMemoCalls.Evaluates.constant (HeapMemoCalls.Evaluates.lookup getQ) rfl
  have numerator : HeapMemoCalls.Evaluates program spec env
      (.binOp (.name "p") .add (.binOp (.constant (.int 2)) .mult (.name "q")))
      heap (number (p+2*q)) heap globals :=
    HeapMemoCalls.Evaluates.binary (HeapMemoCalls.Evaluates.lookup getP) twice rfl
  have denominator : HeapMemoCalls.Evaluates program spec env
      (.binOp (.name "p") .add (.name "q")) heap (number (p+q)) heap globals :=
    HeapMemoCalls.Evaluates.binary (HeapMemoCalls.Evaluates.lookup getP) (HeapMemoCalls.Evaluates.lookup getQ) rfl
  apply HeapMemoCalls.BlockReturns.function (by decide) rfl rfl
  apply HeapMemoCalls.BlockReturns.return_value
  exact HeapMemoCalls.Evaluates.tuple (.cons numerator (.cons denominator .nil))
    (spec_preserves_append heap _) (by simp [pairValues])

private theorem next_pair (n : Nat) (heap : Mutable.Heap) :
    nativePair (heap ++ [.tuple (pairValues
      ((SqrtConvergents.convergent n).1 + 2*(SqrtConvergents.convergent n).2)
      ((SqrtConvergents.convergent n).1 + (SqrtConvergents.convergent n).2))]) (.ref heap.length) (n+1) := by
  refine ⟨heap.length, rfl, ?_⟩
  simp [SqrtConvergents.convergent_next, pairValues, number]

namespace convergent

private abbrev params := ((findFunctionIn program.body "convergent").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "convergent").getD ([], [])).2
private abbrev entry (n : Nat) (globals : Mutable.Globals) : HeapCalls.Env :=
  HeapCalls.functionEnv params sourceBody [convergentNatural n] globals
private abbrev recurse : Expr := .call (.name "convergent")
  [.binOp (.name "n") .sub (.constant (.int 1))]

/-- The actual recursive cached source returns an existing hit reference or the tuple allocated by its real miss body. -/
theorem result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapMemoCalls.ReturnsRel program spec "convergent" [convergentNatural n] heap (PairPost heap n) globals := by
  induction n generalizing heap with
  | zero =>
      apply HeapMemoCalls.BlockReturnsRel.memoized_function (values := [(0 : Int)]) (by decide) rfl rfl
      · apply HeapMemoCalls.BlockReturnsRel.consequence (pre := PairPost heap 0)
        · have getN : entry 0 globals "n" = some (convergentNatural 0) := by cases globals <;> rfl
          have tested : HeapMemoCalls.Evaluates program spec (entry 0 globals)
              (.compare (.name "n") [(.eq, .constant (.int 0))]) heap (.scalar (.bool true)) heap globals :=
            HeapMemoCalls.Evaluates.compare (HeapMemoCalls.Evaluates.lookup getN) HeapMemoCalls.Evaluates.constant rfl
          apply HeapMemoCalls.BlockReturnsRel.branch tested.rel
          rintro value middle ⟨valueEq, heapEq⟩
          subst value
          subst middle
          refine ⟨true, rfl, ?_⟩
          apply HeapMemoCalls.BlockReturnsRel.return_value
          change HeapMemoCalls.EvaluatesRel program spec (entry 0 globals)
            (HeapMemoCalls.pooledTuple baseIdentity [.constant (.int 3), .constant (.int 2)])
            heap (PairPost heap 0) globals
          apply HeapMemoCalls.EvaluatesRel.pooled_tuple
          · have tuple := HeapMemoCalls.Evaluates.tuple (module := program) (spec := spec)
              (env := entry 0 globals) (heap := heap) (globals := globals)
              (.cons (HeapMemoCalls.Evaluates.constant (value := .int 3))
                (.cons (HeapMemoCalls.Evaluates.constant (value := .int 2)) .nil))
              (spec_preserves_append heap [.tuple (pairValues 3 2)]) (by simp)
            apply tuple.rel.consequence
            rintro value after ⟨valueEq, heapEq⟩
            subst value
            subst after
            have pair : HasPair (heap ++ [.tuple (pairValues 3 2)]) (.ref heap.length) 3 2 :=
              ⟨heap.length, rfl, by simp⟩
            exact ⟨⟨[.tuple (pairValues 3 2)], rfl, pair⟩, (spec_base _ _).mpr pair⟩
          · intro value cached
            exact ⟨[], by simp, (spec_base heap value).mp cached⟩
        · rintro value after ⟨extra, shape, pair⟩
          exact ⟨⟨extra, shape, pair⟩, (spec_convergent after 0 value).mpr pair⟩
      · intro value cached
        exact ⟨[], by simp, (spec_convergent heap 0 value).mp cached⟩
  | succ n ih =>
      apply HeapMemoCalls.BlockReturnsRel.memoized_function (values := [((n+1 : Nat) : Int)]) (by decide) rfl rfl
      · apply HeapMemoCalls.BlockReturnsRel.consequence (pre := PairPost heap (n+1))
        · have getN : entry (n+1) globals "n" = some (convergentNatural (n+1)) := by cases globals <;> rfl
          have tested : HeapMemoCalls.Evaluates program spec (entry (n+1) globals)
              (.compare (.name "n") [(.eq, .constant (.int 0))]) heap (.scalar (.bool false)) heap globals := by
            apply HeapMemoCalls.Evaluates.compare (HeapMemoCalls.Evaluates.lookup getN) HeapMemoCalls.Evaluates.constant
            (simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)
          apply HeapMemoCalls.BlockReturnsRel.branch tested.rel
          rintro value middle ⟨valueEq, heapEq⟩
          subst value
          subst middle
          refine ⟨false, rfl, ?_⟩
          apply HeapMemoCalls.BlockReturnsRel.return_value
          have decreased : HeapMemoCalls.Evaluates program spec (entry (n+1) globals)
              (.binOp (.name "n") .sub (.constant (.int 1))) heap (convergentNatural n) heap globals := by
            apply HeapMemoCalls.Evaluates.binary (HeapMemoCalls.Evaluates.lookup getN) HeapMemoCalls.Evaluates.constant
            simp [Mutable.binary, scalarBinary]
          have operand : HeapMemoCalls.EvaluatesRel program spec (entry (n+1) globals) recurse heap (PairPost heap n) globals := by
            apply HeapMemoCalls.EvaluatesRel.call
              (HeapMemoCalls.ArgumentsRel.fixed (.cons decreased .nil))
            rintro values middle ⟨valueEq, heapEq⟩
            subst values
            subst middle
            exact ih heap
          apply HeapMemoCalls.EvaluatesRel.call_star (argumentPost := fun values middle =>
            values = pairValues (SqrtConvergents.convergent n).1 (SqrtConvergents.convergent n).2 ∧
              ∃ extra, middle = heap ++ extra)
          · apply HeapMemoCalls.StarArgumentsRel.star operand
            rintro value middle ⟨extra, shape, address, rfl, found⟩
            refine ⟨pairValues (SqrtConvergents.convergent n).1 (SqrtConvergents.convergent n).2,
              middle, HeapCalls.starItems_tuple middle address _ found, HeapMemoCalls.Cache.Preserves.refl, ?_⟩
            apply HeapMemoCalls.StarArgumentsRel.nil
            exact ⟨by simp, extra, shape⟩
          · rintro values middle ⟨rfl, extra, shape⟩
            apply (next_frac.heapMemo_result (SqrtConvergents.convergent n).1
              (SqrtConvergents.convergent n).2 middle globals).rel.consequence
            rintro value after ⟨valueEq, heapEq⟩
            subst value
            subst after
            refine ⟨extra ++ [.tuple (pairValues
              ((SqrtConvergents.convergent n).1 + 2*(SqrtConvergents.convergent n).2)
              ((SqrtConvergents.convergent n).1 + (SqrtConvergents.convergent n).2))], ?_, next_pair n middle⟩
            rw [shape, List.append_assoc]
        · rintro value after ⟨extra, shape, pair⟩
          exact ⟨⟨extra, shape, pair⟩, (spec_convergent after (n+1) value).mpr pair⟩
      · intro value cached
        exact ⟨[], by simp, (spec_convergent heap (n+1) value).mp cached⟩

end convergent
end data.«project-euler-statements».data.py.project_euler_statements.p57

namespace data.«project-euler-statements».data.py.project_euler_statements.p57
open FormalSW.PyAst
open ProjectEulerSolutions
set_option Elab.async false
private abbrev naiveNatural (value : Nat) : Mutable.Value := .scalar (.int (value : Int))

def digitValues (n : Nat) : List Mutable.Value :=
  (Nat.digits 10 n).map (fun (digit : Nat) => .scalar (.int (digit : Int)))

private theorem common_cache_disjoint : HeapMemoCalls.CacheDisjoint program CommonAst.module := by
  intro name cached
  change name ∈ ["convergent"] at cached
  have same : name = "convergent" := List.mem_singleton.mp cached
  subst name
  exact ⟨by decide, by decide, by decide⟩

/-- The original digits helper runs without touching the tuple cache and preserves every cached object. -/
theorem digits_heapMemo_result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapMemoCalls.ReturnsValue program spec "digits_le" [naiveNatural n] heap (.ref heap.length)
      (heap ++ [.list (digitValues n)]) globals :=
  HeapMemoCalls.ReturnsValue.from_heap common_extension common_cache_disjoint
    (common.digits_le.decimal n heap globals) (spec_preserves_append heap _)

/-- Scalar results retain the entire original caller heap as a prefix. -/
def ScalarPost (heap : Mutable.Heap) (expected : Mutable.Value) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  value = expected ∧ ∃ extra, after = heap ++ extra

private theorem ScalarPost.frame {heap middle after : Mutable.Heap} {extra : Mutable.Heap}
    {expected value : Mutable.Value} (shape : middle = heap ++ extra)
    (holds : ScalarPost middle expected value after) : ScalarPost heap expected value after := by
  obtain ⟨equal, tail, final⟩ := holds
  exact ⟨equal, extra ++ tail, by rw [final, shape, List.append_assoc]⟩

namespace naive

private def component (n : Nat) (second : Bool) : Nat :=
  if second then (SqrtConvergents.convergent n).2 else (SqrtConvergents.convergent n).1
private def position (second : Bool) : Int := if second then 1 else 0
private abbrev componentExpression (second : Bool) : Expr :=
  .subscript (.call (.name "convergent") [.name "i"]) (.constant (.int (position second)))
private abbrev lengthExpression (second : Bool) : Expr :=
  .builtinCall .len [.call (.name "digits_le") [componentExpression second]]
private abbrev testExpression : Expr := .compare (lengthExpression false) [(.gt, lengthExpression true)]
private abbrev loopBody : List Stmt :=
  [.ifThen testExpression (HeapCalls.sumBody (.constant (.int 1)) []) []]

/-- Each component access makes its own real cached convergent call before reading the original returned tuple. -/
private theorem component_result (n : Nat) (second : Bool) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getI : env "i" = some (naiveNatural n)) :
    HeapMemoCalls.EvaluatesRel program spec env (componentExpression second) heap
      (ScalarPost heap (naiveNatural (component n second))) globals := by
  have fraction : HeapMemoCalls.EvaluatesRel program spec env (.call (.name "convergent") [.name "i"])
      heap (PairPost heap n) globals := by
    apply HeapMemoCalls.EvaluatesRel.call
      (HeapMemoCalls.ArgumentsRel.fixed (.cons (HeapMemoCalls.Evaluates.lookup getI) .nil))
    rintro values middle ⟨valueEq, heapEq⟩
    subst values
    subst middle
    exact convergent.result n heap globals
  apply HeapMemoCalls.EvaluatesRel.subscript
    (b := .constant (.int (position second))) (ordinary := by intros; simp) fraction
    (fun _ middle _ => HeapMemoCalls.EvaluatesRel.constant (post := fun value after =>
      value = number (position second) ∧ after = middle) ⟨rfl, rfl⟩)
  rintro av middle bv afterIndex pair ⟨indexEq, afterIndexEq⟩
  subst bv
  subst afterIndex
  obtain ⟨extra, shape, address, rfl, found⟩ := pair
  refine ⟨naiveNatural (component n second), middle, ?_, HeapMemoCalls.Cache.Preserves.refl, rfl, extra, shape⟩
  cases second <;> simp [component, position, Mutable.getItem, Mutable.index, found, pairValues, number, naiveNatural, Except.map]

private def DigitsPost (heap : Mutable.Heap) (n : Nat) (value : Mutable.Value) (after : Mutable.Heap) : Prop :=
  ∃ extra address, after = heap ++ extra ∧ value = .ref address ∧ after[address]? = some (.list (digitValues n))

private theorem digits_component_result (n : Nat) (second : Bool) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getI : env "i" = some (naiveNatural n)) :
    HeapMemoCalls.EvaluatesRel program spec env (.call (.name "digits_le") [componentExpression second])
      heap (DigitsPost heap (component n second)) globals := by
  apply HeapMemoCalls.EvaluatesRel.call (argumentPost := fun values middle =>
    values = [naiveNatural (component n second)] ∧ ∃ extra, middle = heap ++ extra)
  · apply HeapMemoCalls.ArgumentsRel.cons (component_result n second heap env globals getI)
    rintro value middle ⟨rfl, extra, shape⟩
    exact HeapMemoCalls.ArgumentsRel.nil ⟨rfl, extra, shape⟩
  · rintro values middle ⟨rfl, extra, shape⟩
    apply (digits_heapMemo_result (component n second) middle globals).rel.consequence
    rintro value after ⟨valueEq, heapEq⟩
    subst value
    subst after
    exact ⟨extra ++ [.list (digitValues (component n second))], middle.length,
      by rw [shape, List.append_assoc], rfl, by simp⟩

/-- The real digit allocation is retained while len returns its exact positional length. -/
private theorem length_result (n : Nat) (second : Bool) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getI : env "i" = some (naiveNatural n)) :
    HeapMemoCalls.EvaluatesRel program spec env (lengthExpression second) heap
      (ScalarPost heap (naiveNatural (Nat.digits 10 (component n second)).length)) globals := by
  apply HeapMemoCalls.EvaluatesRel.builtin (argumentPost := fun values middle =>
    ∃ value, values = [value] ∧ DigitsPost heap (component n second) value middle)
  · apply HeapMemoCalls.ArgumentsRel.cons (digits_component_result n second heap env globals getI)
    intro value middle holds
    exact HeapMemoCalls.ArgumentsRel.nil ⟨value, rfl, holds⟩
  · rintro values middle ⟨value, rfl, extra, address, shape, rfl, found⟩
    refine ⟨naiveNatural (Nat.digits 10 (component n second)).length, middle, ?_,
      HeapMemoCalls.Cache.Preserves.refl, rfl, extra, shape⟩
    simp [HeapCalls.primitive, Mutable.length, found, digitValues]

/-- Both original convergent calls and both digits_le allocations execute, in their source order. -/
private theorem test_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getI : env "i" = some (naiveNatural n)) :
    HeapMemoCalls.EvaluatesRel program spec env testExpression heap
      (ScalarPost heap (.scalar (.bool (decide
        ((Nat.digits 10 (SqrtConvergents.convergent n).2).length <
          (Nat.digits 10 (SqrtConvergents.convergent n).1).length))))) globals := by
  apply HeapMemoCalls.EvaluatesRel.compare (length_result n false heap env globals getI)
    (fun _ middle _ => length_result n true middle env globals getI)
  rintro av middle bv afterRight ⟨rfl, firstExtra, firstShape⟩ ⟨rfl, secondExtra, secondShape⟩
  refine ⟨.scalar (.bool (decide
    ((Nat.digits 10 (SqrtConvergents.convergent n).2).length <
      (Nat.digits 10 (SqrtConvergents.convergent n).1).length))), afterRight, ?_,
    HeapMemoCalls.Cache.Preserves.refl, rfl, firstExtra ++ secondExtra, ?_⟩
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp, component]
  · rw [secondShape, firstShape, List.append_assoc]

/-- Finite generator traversal keeps all cache and allocation effects while summing the actual accepted expansions. -/
private theorem loop (length first : Nat) (stop : Int) (equation : stop = ((first+length : Nat) : Int))
    (heap : Mutable.Heap) (env : HeapCalls.Env) (initial : Nat) (globals : Mutable.Globals)
    (accumulator : env HeapCalls.sumAccumulator = some (naiveNatural initial)) :
    HeapMemoCalls.BlockReturnsRel program spec env
      [.rangeStepLoop "i" first stop 1 loopBody [], .return (.name HeapCalls.sumAccumulator)] heap
      (ScalarPost heap (naiveNatural (initial + SqrtConvergents.sumFrom first length))) globals := by
  induction length generalizing first heap env initial with
  | zero =>
      simp only [SqrtConvergents.sumFrom_zero, Nat.add_zero]
      apply HeapMemoCalls.BlockReturnsRel.range_done (by simp [Calls.rangeContinues]; omega)
      exact HeapMemoCalls.BlockReturnsRel.return_value
        (HeapMemoCalls.EvaluatesRel.lookup accumulator ⟨rfl, [], by simp⟩)
  | succ length ih =>
      let bound := HeapCalls.setLocal env "i" (naiveNatural first)
      have boundAccumulator : bound HeapCalls.sumAccumulator = some (naiveNatural initial) := by
        simpa [bound, HeapCalls.setLocal, HeapCalls.sumAccumulator] using accumulator
      have tested := test_result first heap bound globals rfl
      apply HeapMemoCalls.BlockReturnsRel.range_step (by simp [Calls.rangeContinues]; omega)
      apply HeapMemoCalls.BlockReturnsRel.branch tested
      rintro value middle ⟨rfl, extra, shape⟩
      by_cases more : (Nat.digits 10 (SqrtConvergents.convergent first).2).length <
          (Nat.digits 10 (SqrtConvergents.convergent first).1).length
      · have accepted : SqrtConvergents.weight first = 1 := by simp [SqrtConvergents.weight, SqrtConvergents.indicator, more]
        refine ⟨true, by simp [Mutable.truth, scalarTruth, more], ?_⟩
        apply HeapMemoCalls.BlockReturnsRel.assign
          (HeapMemoCalls.Evaluates.binary (value := naiveNatural (initial+1)) (finalHeap := middle)
            (HeapMemoCalls.Evaluates.lookup boundAccumulator) HeapMemoCalls.Evaluates.constant rfl).rel
        rintro value afterCounter ⟨valueEq, heapEq⟩
        subst value
        subst afterCounter
        let updated := HeapCalls.setLocal bound HeapCalls.sumAccumulator (naiveNatural (initial+1))
        have updatedAccumulator : updated HeapCalls.sumAccumulator = some (naiveNatural (initial+1)) := by
          simp [updated, HeapCalls.setLocal]
        have rest := ih (first+1) (by omega) middle updated (initial+1) updatedAccumulator
        have framed := rest.consequence (fun value after holds => ScalarPost.frame shape holds)
        simpa only [SqrtConvergents.sumFrom_succ, accepted, Nat.add_assoc, loopBody, HeapCalls.sumBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, if_false] using framed
      · have rejected : SqrtConvergents.weight first = 0 := by simp [SqrtConvergents.weight, SqrtConvergents.indicator, more]
        refine ⟨false, by simp [Mutable.truth, scalarTruth, more], ?_⟩
        have rest := ih (first+1) (by omega) middle bound initial boundAccumulator
        have framed := rest.consequence (fun value after holds => ScalarPost.frame shape holds)
        simpa only [SqrtConvergents.sumFrom_succ, rejected, Nat.zero_add, loopBody, HeapCalls.sumBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, if_false] using framed

private abbrev params := ((findFunctionIn program.body "naive").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
private abbrev testedBounds : List Expr := [.name "k"]

/-- The original recursive memoized reference counts exactly its native structural model for every signed limit. -/
theorem result (limit : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapMemoCalls.ReturnsRel program spec "naive" [number limit] heap
      (ScalarPost heap (naiveNatural (ProjectEulerStatements.P57.naive limit.toNat))) globals := by
  let env := HeapCalls.functionEnv params sourceBody [number limit] globals
  let inside := HeapCalls.setLocal
    (HeapCalls.comprehensionEnv env [("i", .call (.name "range") testedBounds, [testExpression])])
    HeapCalls.sumAccumulator (naiveNatural 0)
  have getLimit : env "k" = some (number limit) := by cases globals <;> rfl
  have initialized : inside HeapCalls.sumAccumulator = some (naiveNatural 0) := by simp [inside, HeapCalls.setLocal]
  apply HeapMemoCalls.BlockReturnsRel.function (by decide) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.return_value
  apply HeapMemoCalls.EvaluatesRel.sum_range
  apply HeapMemoCalls.EvaluatesRel.sum_generator_range
    (middle := heap) (afterStart := heap)
    (.cons (HeapMemoCalls.Evaluates.lookup getLimit) .nil) rfl HeapMemoCalls.Evaluates.constant rfl
  by_cases nonnegative : 0 ≤ limit
  · have executed := loop limit.toNat 0 limit (by omega) heap inside 0 globals initialized
    simpa only [inside, HeapCalls.comprehensionFilters, HeapCalls.sumBody, List.foldr_cons, List.foldr_nil,
      loopBody, Nat.zero_add, ← SqrtConvergents.naive_eq_sumFrom] using executed
  · have empty : limit.toNat = 0 := by omega
    simp only [empty, ProjectEulerStatements.P57.naive, List.range_zero, List.foldl_nil]
    apply HeapMemoCalls.BlockReturnsRel.range_done (by simp [Calls.rangeContinues]; omega)
    exact HeapMemoCalls.BlockReturnsRel.return_value
      (HeapMemoCalls.EvaluatesRel.lookup initialized ⟨rfl, [], by simp⟩)

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p57

namespace data.«project-euler-statements».data.py.project_euler_statements.p57.naive
open FormalSW.PyAst

theorem «Returns» (limit : Int) :
    (HeapMemoCalls.scalarFunction P57Ast.module "naive" [.int limit]).Returns :=
  (result limit []).scalar_returns

theorem «Supported» (limit : Int) :
    (HeapMemoCalls.scalarFunction P57Ast.module "naive" [.int limit]).Supported :=
  («Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p57.naive
