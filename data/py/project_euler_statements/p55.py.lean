import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p55.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerSolutions.Lib.Lychrel
import ProjectEulerSolutions.Lib.HeapCollection
import lang.py.FormalSW.TruthCalls
import lang.py.FormalSW.SumCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p55
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev program := P55Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)

def digitValues (n : Nat) : List Mutable.Value := (Nat.digits 10 n).map number

def scalarScratch (n : Nat) : Mutable.Heap := [Mutable.Object.list (digitValues n), Mutable.Object.list ((digitValues n).reverse)]
def scalarHeap (heap : Mutable.Heap) (n : Nat) : Mutable.Heap := heap ++ scalarScratch n

/-- Linking retains the original common helper bodies and their ordinary defaults. -/
private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := P55Ast.module.body.take 11 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["reverse_digits", "is_palindrome", "reverse_add", "iterate", "pal_at",
      "reaches_palindrome", "is_lychrel", "naive", "naive_default",
      "__formalsw_callback_iterate_f_reverse_add"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

/-- Actual source call to digits_le, with its default decimal base and live global context. -/
theorem digits_result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "digits_le" [number n] heap (.ref heap.length)
      (heap ++ [Mutable.Object.list (digitValues n)]) globals :=
  (common.digits_le.decimal n heap globals).extend common_extension

/-- The actual one-argument positional helper call expands its source default base ten. -/
theorem of_digits_decimal (digits : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (Mutable.Object.list (digits.map fun digit => .scalar (.int digit))))
    (globals : Mutable.Globals := []) :
    ReturnsValue program "of_digits_le" [.ref address] heap
      (.scalar (.int (ProjectEulerStatements.PositionalDigits.value 10 digits))) heap globals :=
  (ReturnsValue.with_defaults rfl rfl rfl (common.of_digits_le.result digits 10 heap address found globals)).extend common_extension

/-- Both digit-conversion helpers leave every caller object untouched. -/
theorem scalarHeap_caller (heap : Mutable.Heap) (n address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : (scalarHeap heap n)[address]? = some object :=
  HeapCollection.prefix_found heap (scalarScratch n) address object found

namespace reverse_digits

/-- The original nested calls allocate a digit list and its reversed copy, then evaluate the reversed digits. -/
theorem expression (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getN : env "n" = some (number n)) :
    Evaluates program env (.call (.name "of_digits_le") [.reversedList (.call (.name "digits_le") [.name "n"])])
      heap (number (Lychrel.reverse n)) (scalarHeap heap n) globals := by
  have extracted : Evaluates program env (.call (.name "digits_le") [.name "n"]) heap (.ref heap.length)
      (heap ++ [Mutable.Object.list (digitValues n)]) globals :=
    Evaluates.call (.cons (Evaluates.lookup getN) .nil) (digits_result n heap globals)
  have reversed : Evaluates program env (.reversedList (.call (.name "digits_le") [.name "n"])) heap
      (.ref (heap.length+1)) (scalarHeap heap n) globals := by
    simpa only [scalarHeap, scalarScratch, List.length_append, List.length_singleton,
      List.append_assoc, List.cons_append, List.nil_append] using
      Evaluates.reversed_list extracted (by simp)
  have copied : (scalarHeap heap n)[heap.length+1]? =
      some (Mutable.Object.list (((Nat.digits 10 n).reverse.map fun (digit : Nat) => (digit : Int)).map
        fun digit => .scalar (.int digit))) := by
    simp only [List.map_map, Function.comp_def]
    change (scalarHeap heap n)[heap.length+1]? = some (Mutable.Object.list ((Nat.digits 10 n).reverse.map number))
    rw [List.map_reverse]
    simp [scalarHeap, scalarScratch, digitValues]
  have converted := of_digits_decimal ((Nat.digits 10 n).reverse.map fun (digit : Nat) => (digit : Int))
    (scalarHeap heap n) (heap.length+1) copied globals
  have valueEq : ProjectEulerStatements.PositionalDigits.value 10
      ((Nat.digits 10 n).reverse.map fun (digit : Nat) => (digit : Int)) = (Lychrel.reverse n : Int) := by
    simpa only [Lychrel.reverse] using
      ProjectEulerStatements.PositionalDigits.value_naturals 10 (Nat.digits 10 n).reverse
  rw [valueEq] at converted
  exact Evaluates.call (.cons reversed .nil) converted

/-- Actual reverse_digits source correctness for every nonnegative integer, including zero. -/
theorem result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "reverse_digits" [number n] heap (number (Lychrel.reverse n)) (scalarHeap heap n) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact expression n heap _ globals (by cases globals <;> rfl)

end reverse_digits

namespace is_palindrome

/-- Equality of the original digit list and the actual reversed copy is decimal-digit palindromicity. -/
theorem test (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getDigits : env "ds" = some (.ref heap.length)) :
    Evaluates program env (.compare (.name "ds") [(.eq, .reversedList (.name "ds"))])
      (heap ++ [Mutable.Object.list (digitValues n)]) (.scalar (.bool (Lychrel.palindrome n))) (scalarHeap heap n) globals := by
  have tested : Evaluates program env (.compare (.name "ds") [(.eq, .reversedList (.name "ds"))])
      (heap ++ [Mutable.Object.list (digitValues n)]) (.scalar (.bool (Lychrel.palindrome n)))
      ((heap ++ [Mutable.Object.list (digitValues n)]) ++ [Mutable.Object.list ((digitValues n).reverse)]) globals := by
    apply Evaluates.compare (Evaluates.lookup getDigits)
      (Evaluates.reversed_list (items := digitValues n) (Evaluates.lookup getDigits) (by simp))
    have originalFound :
        ((heap ++ [Mutable.Object.list (digitValues n)]) ++ [Mutable.Object.list ((digitValues n).reverse)])[heap.length]? =
          some (Mutable.Object.list (((Nat.digits 10 n).map fun (digit : Nat) => (digit : Int)).map
            fun digit => .scalar (.int digit))) := by
      simp only [List.map_map, Function.comp_def]
      change ((heap ++ [Mutable.Object.list (digitValues n)]) ++ [Mutable.Object.list ((digitValues n).reverse)])[heap.length]? =
        some (Mutable.Object.list (digitValues n))
      simp
    have reversedFound :
        ((heap ++ [Mutable.Object.list (digitValues n)]) ++ [Mutable.Object.list ((digitValues n).reverse)])[(heap ++ [Mutable.Object.list (digitValues n)]).length]? =
          some (Mutable.Object.list (((Nat.digits 10 n).reverse.map fun (digit : Nat) => (digit : Int)).map
            fun digit => .scalar (.int digit))) := by
      simp only [List.map_map, Function.comp_def]
      change ((heap ++ [Mutable.Object.list (digitValues n)]) ++ [Mutable.Object.list ((digitValues n).reverse)])[(heap ++ [Mutable.Object.list (digitValues n)]).length]? =
          some (Mutable.Object.list ((Nat.digits 10 n).reverse.map number))
      rw [List.map_reverse]
      change ((heap ++ [Mutable.Object.list (digitValues n)]) ++ [Mutable.Object.list ((digitValues n).reverse)])[(heap ++ [Mutable.Object.list (digitValues n)]).length]? = some (Mutable.Object.list ((digitValues n).reverse))
      simp
    have compared := HeapCalls.compare_int_lists
      ((Nat.digits 10 n).map fun (digit : Nat) => (digit : Int))
      ((Nat.digits 10 n).reverse.map fun (digit : Nat) => (digit : Int)) originalFound reversedFound
    have injective : Function.Injective (List.map fun digit : Nat => (digit : Int)) :=
      List.map_injective_iff.mpr Nat.cast_injective
    simpa only [Lychrel.palindrome, injective.eq_iff] using compared
  simpa only [scalarHeap, scalarScratch, List.append_assoc, List.cons_append, List.nil_append] using tested

/-- The original source composes default digits_le with its real list equality and reversed-list allocation. -/
theorem result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "is_palindrome" [number n] heap (.scalar (.bool (Lychrel.palindrome n))) (scalarHeap heap n) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign
    (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (digits_result n heap globals))
  apply BlockReturns.return_value
  exact test n heap _ globals rfl

end is_palindrome

namespace reverse_add

/-- Reverse-and-add uses the original source call, arbitrary-precision integer addition and the same private two lists. -/
theorem result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "reverse_add" [number n] heap (number (Lychrel.step n)) (scalarHeap heap n) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (Evaluates.lookup (by cases globals <;> rfl))
    (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (reverse_digits.result n heap globals))
  simp [Mutable.binary, scalarBinary, Lychrel.step]

end reverse_add

end data.«project-euler-statements».data.py.project_euler_statements.p55

namespace data.«project-euler-statements».data.py.project_euler_statements.p55
open FormalSW.PyAst

theorem reverse_digits.«Returns» (n : Int)
    (condition : Calls.Condition P55Ast.module (fun key => if key = "n" then some (.int n) else none)
      P55Ast.requires_reverse_digits_0) :
    (HeapCalls.scalarFunction P55Ast.module "reverse_digits" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  have returned : (HeapCalls.scalarFunction P55Ast.module "reverse_digits" [.int (n.toNat : Int)]).Returns :=
    (reverse_digits.result n.toNat []).scalar_returns
  simpa only [Int.toNat_of_nonneg nonnegative] using returned

theorem reverse_digits.«Supported» (n : Int)
    (condition : Calls.Condition P55Ast.module (fun key => if key = "n" then some (.int n) else none)
      P55Ast.requires_reverse_digits_0) :
    (HeapCalls.scalarFunction P55Ast.module "reverse_digits" [.int n]).Supported :=
  (reverse_digits.«Returns» n condition).supported

theorem is_palindrome.«Returns» (n : Int)
    (condition : Calls.Condition P55Ast.module (fun key => if key = "n" then some (.int n) else none)
      P55Ast.requires_is_palindrome_0) :
    (HeapCalls.scalarFunction P55Ast.module "is_palindrome" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  have returned : (HeapCalls.scalarFunction P55Ast.module "is_palindrome" [.int (n.toNat : Int)]).Returns :=
    (is_palindrome.result n.toNat []).scalar_returns
  simpa only [Int.toNat_of_nonneg nonnegative] using returned

theorem is_palindrome.«Supported» (n : Int)
    (condition : Calls.Condition P55Ast.module (fun key => if key = "n" then some (.int n) else none)
      P55Ast.requires_is_palindrome_0) :
    (HeapCalls.scalarFunction P55Ast.module "is_palindrome" [.int n]).Supported :=
  (is_palindrome.«Returns» n condition).supported

theorem reverse_add.«Returns» (n : Int)
    (condition : Calls.Condition P55Ast.module (fun key => if key = "n" then some (.int n) else none)
      P55Ast.requires_reverse_add_0) :
    (HeapCalls.scalarFunction P55Ast.module "reverse_add" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  have returned : (HeapCalls.scalarFunction P55Ast.module "reverse_add" [.int (n.toNat : Int)]).Returns :=
    (reverse_add.result n.toNat []).scalar_returns
  simpa only [Int.toNat_of_nonneg nonnegative] using returned

theorem reverse_add.«Supported» (n : Int)
    (condition : Calls.Condition P55Ast.module (fun key => if key = "n" then some (.int n) else none)
      P55Ast.requires_reverse_add_0) :
    (HeapCalls.scalarFunction P55Ast.module "reverse_add" [.int n]).Supported :=
  (reverse_add.«Returns» n condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p55


namespace data.«project-euler-statements».data.py.project_euler_statements.p55
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

namespace iterate_source
private abbrev program := P55Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev clone := "__formalsw_callback_iterate_f_reverse_add"
private abbrev loopBody : List Stmt :=
  [.assign [.name "n"] (.call (.name "reverse_add") [.name "n"])]

private theorem loop (fuel n : Nat) (next stop : Int) (remaining : stop-next = (fuel : Int))
    (heap : Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getN : env "n" = some (number n)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "_" next stop 1 loopBody [], .return (.name "n")]
      heap (number (Lychrel.iterate fuel n)) (heap ++ extra) globals := by
  induction fuel generalizing n next heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil, Lychrel.iterate_zero]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getN)
  | succ fuel ih =>
      let bound := setLocal env "_" (number next)
      let advanced := setLocal bound "n" (number (Lychrel.step n))
      have boundN : bound "n" = some (number n) := by simpa [bound, setLocal] using getN
      have advancedN : advanced "n" = some (number (Lychrel.step n)) := by simp [advanced, setLocal]
      have reversed := reverse_add.result n heap globals
      obtain ⟨extra, continued⟩ := ih (Lychrel.step n) (next+1) (by omega) (scalarHeap heap n) advanced advancedN
      refine ⟨scalarScratch n ++ extra, ?_⟩
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup boundN) .nil) reversed)
      simpa only [Lychrel.iterate_succ, loopBody, Calls.loopContinuation,
        show Calls.loopControl loopBody = false from rfl, Bool.false_eq_true, if_false,
        List.singleton_append, scalarHeap, List.append_assoc] using continued

private abbrev sourceBody := ((findFunctionIn program.body clone).getD ([], [])).2

/-- The checked named-callback clone executes the original iterate loop, including empty signed ranges. -/
theorem result (n : Nat) (k : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program clone [.scalar (.int k), number n] heap
      (number (Lychrel.iterate k.toNat n)) (heap ++ extra) globals := by
  let args := ((findFunctionIn program.body clone).getD ([], [])).1
  let env := functionEnv args sourceBody [.scalar (.int k), number n] globals
  have getK : env "k" = some (.scalar (.int k)) := by cases globals <;> rfl
  have getN : env "n" = some (number n) := by cases globals <;> rfl
  by_cases positive : 0 < k
  · obtain ⟨extra, ran⟩ := loop k.toNat n 0 k (by omega) heap env globals getN
    refine ⟨extra, ?_⟩
    apply BlockReturns.function rfl rfl
    exact BlockReturns.for_range (.cons (Evaluates.lookup getK) .nil) rfl ran
  · have empty : k.toNat = 0 := by omega
    refine ⟨[], ?_⟩
    simp only [empty, Lychrel.iterate_zero, List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.for_range (.cons (Evaluates.lookup getK) .nil) rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup getN)

end iterate_source

namespace pal_at
private abbrev program := P55Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev params := ((findFunctionIn program.body "pal_at").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "pal_at").getD ([], [])).2

/-- The original nested source call evaluates its named callback iteration before checking the resulting digits. -/
theorem result (n : Nat) (k : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "pal_at" [number n, number k] heap
      (flag (Lychrel.palindrome (Lychrel.iterate k.toNat n))) (heap ++ extra) globals := by
  let env := functionEnv params sourceBody [number n, number k] globals
  have getN : env "n" = some (number n) := by cases globals <;> rfl
  have getK : env "k" = some (number k) := by cases globals <;> rfl
  obtain ⟨extra, iterated⟩ := iterate_source.result n k heap globals
  have called := Evaluates.call (.cons (Evaluates.lookup getK) (.cons (Evaluates.lookup getN) .nil)) iterated
  have finished : ReturnsValue program "pal_at" [number n, number k] heap
      (flag (Lychrel.palindrome (Lychrel.iterate k.toNat n)))
      (scalarHeap (heap ++ extra) (Lychrel.iterate k.toNat n)) globals := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.call (.cons called .nil) (is_palindrome.result (Lychrel.iterate k.toNat n) (heap ++ extra) globals)
  exact ⟨extra ++ scalarScratch (Lychrel.iterate k.toNat n), by simpa only [scalarHeap, List.append_assoc] using finished⟩

end pal_at
end data.«project-euler-statements».data.py.project_euler_statements.p55


namespace data.«project-euler-statements».data.py.project_euler_statements.p55
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

namespace reaches_palindrome
private abbrev program := P55Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev tested : Expr := .call (.name "pal_at") [.name "n", .name "k"]
private abbrev loopBody := truthBody false tested
private def predicate (n : Nat) (k : Nat) : Bool := Lychrel.palindrome (Lychrel.iterate k n)

def value (n : Nat) (maxIters : Int) : Bool := (List.range' 1 maxIters.toNat).any (predicate n)

/-- Each lazy-any callback executes the original repeated iteration and retains its private allocations. -/
private theorem loop (length first n : Nat) (stop : Int) (equation : stop = ((first+length : Nat) : Int))
    (heap : Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getN : env "n" = some (number n)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "k" first stop 1 loopBody [], .return (.constant (.bool false))]
      heap (flag ((List.range' first length).any (predicate n))) (heap ++ extra) globals := by
  induction length generalizing first heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.range'_zero, List.any_nil, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ length ih =>
      let bound := setLocal env "k" (number first)
      have boundN : bound "n" = some (number n) := by simpa [bound, setLocal] using getN
      obtain ⟨firstExtra, called⟩ := pal_at.result n first heap globals
      have testedRun : Evaluates program bound tested heap (flag (predicate n first)) (heap ++ firstExtra) globals := by
        simpa only [predicate, Int.toNat_natCast] using Evaluates.call
          (.cons (Evaluates.lookup boundN) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil)) called
      cases accepted : predicate n first with
      | true =>
          refine ⟨firstExtra, ?_⟩
          simp only [List.range'_succ, List.any_cons, accepted, Bool.true_or]
          apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using testedRun) rfl
          exact BlockReturns.return_value Evaluates.constant
      | false =>
          obtain ⟨restExtra, continued⟩ := ih (first+1) (by omega) (heap ++ firstExtra) bound boundN
          refine ⟨firstExtra ++ restExtra, ?_⟩
          simp only [List.range'_succ, List.any_cons, accepted, Bool.false_or]
          apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using testedRun) rfl
          simpa only [loopBody, truthBody, Calls.loopContinuation,
            show Calls.loopControl loopBody = false from rfl, Bool.false_eq_true, if_false,
            List.nil_append, Int.natCast_add, Int.natCast_one, List.append_assoc] using continued

private abbrev params := ((findFunctionIn program.body "reaches_palindrome").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "reaches_palindrome").getD ([], [])).2
private abbrev bounds : List Expr := [.constant (.int 1), .binOp (.name "max_iters") .add (.constant (.int 1))]

/-- The corrected original any generator tests positive steps one through the cap, with no step-zero acceptance. -/
theorem result (n : Nat) (maxIters : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "reaches_palindrome" [number n, number maxIters] heap
      (flag (value n maxIters)) (heap ++ extra) globals := by
  let env := functionEnv params sourceBody [number n, number maxIters] globals
  let inside := comprehensionTargetsEnv env [(.name "k", .call (.name "range") bounds, [])]
  have getN : env "n" = some (number n) := by cases globals <;> rfl
  have getMax : env "max_iters" = some (number maxIters) := by cases globals <;> rfl
  have innerN : inside "n" = some (number n) := by
    simpa [inside, comprehensionTargetsEnv, targetLocals] using getN
  have arguments : Evaluates.Arguments program env bounds heap [number 1, number (maxIters+1)] heap globals :=
    .cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup getMax) Evaluates.constant rfl) .nil)
  by_cases positive : 0 < maxIters
  · obtain ⟨extra, ran⟩ := loop maxIters.toNat 1 n (maxIters+1) (by omega) heap inside globals innerN
    refine ⟨extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.truth_generator_range (universal := false) (target := .name "k")
      (filters := []) (generators := []) arguments rfl
    simpa only [comprehensionTargetName, comprehensionTargetBody, comprehensionFilters, comprehensionTargetsBody,
      List.foldr_nil, value] using ran
  · have empty : maxIters.toNat = 0 := by omega
    refine ⟨[], ?_⟩
    simp only [value, empty, List.range'_zero, List.any_nil, List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.truth_generator_range (universal := false) (target := .name "k")
      (filters := []) (generators := []) arguments rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value Evaluates.constant

end reaches_palindrome

namespace is_lychrel
private abbrev program := P55Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev params := ((findFunctionIn program.body "is_lychrel").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "is_lychrel").getD ([], [])).2

/-- Negating the original lazy scan computes the same positive-step candidate predicate as the optimized loop. -/
theorem result (n : Nat) (maxIters : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "is_lychrel" [number n, number maxIters] heap
      (flag (Lychrel.candidate n maxIters.toNat)) (heap ++ extra) globals := by
  let env := functionEnv params sourceBody [number n, number maxIters] globals
  have getN : env "n" = some (number n) := by cases globals <;> rfl
  have getMax : env "max_iters" = some (number maxIters) := by cases globals <;> rfl
  obtain ⟨extra, reached⟩ := reaches_palindrome.result n maxIters heap globals
  refine ⟨extra, ?_⟩
  rw [Lychrel.candidate_eq_not_any]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.unary
    (Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getMax) .nil)) reached)
  rfl

end is_lychrel
end data.«project-euler-statements».data.py.project_euler_statements.p55


namespace data.«project-euler-statements».data.py.project_euler_statements.p55
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

namespace naive
private abbrev program := P55Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev tested : Expr := .call (.name "is_lychrel") [.name "x", .name "max_iters"]
private abbrev loopBody : List Stmt := [.ifThen tested (sumBody (.constant (.int 1)) []) []]
private def indicator (maxIters : Int) (n : Nat) : Int := if Lychrel.candidate n maxIters.toNat then 1 else 0

private theorem filter_step (n : Nat) (maxIters : Int) (heap : Heap) (env : HeapCalls.Env)
    (initial : Int) (globals : Mutable.Globals)
    (getX : env "x" = some (number n)) (getMax : env "max_iters" = some (number maxIters))
    (accumulator : env sumAccumulator = some (number initial)) :
    ∃ extra finalEnv, BlockContinues program env loopBody heap finalEnv (heap ++ extra) globals ∧
      finalEnv "max_iters" = some (number maxIters) ∧
      finalEnv sumAccumulator = some (number (initial + indicator maxIters n)) := by
  obtain ⟨extra, ran⟩ := is_lychrel.result n maxIters heap globals
  have evaluated : Evaluates program env tested heap (flag (Lychrel.candidate n maxIters.toNat)) (heap ++ extra) globals :=
    Evaluates.call (.cons (Evaluates.lookup getX) (.cons (Evaluates.lookup getMax) .nil)) ran
  cases accepted : Lychrel.candidate n maxIters.toNat with
  | false =>
      refine ⟨extra, env, ?_, getMax, ?_⟩
      · apply BlockContinues.branch (flag := false) (by simpa only [accepted] using evaluated) rfl
        exact BlockContinues.nil
      · simpa only [indicator, accepted, Bool.false_eq_true, if_false, Int.add_zero] using accumulator
  | true =>
      refine ⟨extra, setLocal env sumAccumulator (number (initial+1)), ?_, ?_, ?_⟩
      · apply BlockContinues.branch (flag := true) (by simpa only [accepted] using evaluated) rfl
        apply BlockContinues.assign
        exact Evaluates.binary (Evaluates.lookup accumulator) Evaluates.constant rfl
      · simpa [setLocal, sumAccumulator] using getMax
      · simp [setLocal, indicator, accepted]

/-- The actual counting generator retains all callback effects while adding one only for a true candidate. -/
private theorem loop (length first : Nat) (stop : Int) (equation : stop = ((first+length : Nat) : Int))
    (maxIters : Int) (heap : Heap) (env : HeapCalls.Env) (initial : Int) (globals : Mutable.Globals)
    (getMax : env "max_iters" = some (number maxIters))
    (accumulator : env sumAccumulator = some (number initial)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "x" first stop 1 loopBody [], .return (.name sumAccumulator)]
      heap (number (initial + ((List.range' first length).map (indicator maxIters)).sum)) (heap ++ extra) globals := by
  induction length generalizing first heap env initial with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.range'_zero, List.map_nil, List.sum_nil, Int.add_zero, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup accumulator)
  | succ length ih =>
      let bound := setLocal env "x" (number first)
      have boundMax : bound "max_iters" = some (number maxIters) := by simpa [bound, setLocal] using getMax
      have boundAccumulator : bound sumAccumulator = some (number initial) := by
        simpa [bound, setLocal, sumAccumulator] using accumulator
      obtain ⟨firstExtra, nextEnv, stepped, nextMax, nextAccumulator⟩ :=
        filter_step first maxIters heap bound initial globals (by simp [bound, setLocal]) boundMax boundAccumulator
      obtain ⟨restExtra, continued⟩ := ih (first+1) (by omega) (heap ++ firstExtra) nextEnv
        (initial + indicator maxIters first) nextMax nextAccumulator
      refine ⟨firstExtra ++ restExtra, ?_⟩
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [loopBody, sumBody, Calls.loopContinuation,
        show Calls.loopControl loopBody = false from rfl, Bool.false_eq_true, if_false,
        List.range'_succ, List.map_cons, List.sum_cons, Int.natCast_add, Int.natCast_one,
        Int.add_assoc, List.append_assoc] using stepped.returns continued

private abbrev params := ((findFunctionIn program.body "naive").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
private abbrev bounds : List Expr := [.constant (.int 1), .name "n"]

/-- The corrected original source omits zero and counts the same finite candidate predicate for every signed limit/cap. -/
theorem result (limit maxIters : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number limit, number maxIters] heap
      (number (Lychrel.count limit.toNat maxIters.toNat)) (heap ++ extra) globals := by
  let env := functionEnv params sourceBody [number limit, number maxIters] globals
  let inside := setLocal
    (comprehensionEnv env [("x", .call (.name "range") bounds, [tested])]) sumAccumulator (number 0)
  have getLimit : env "n" = some (number limit) := by cases globals <;> rfl
  have getMax : env "max_iters" = some (number maxIters) := by cases globals <;> rfl
  have innerMax : inside "max_iters" = some (number maxIters) := by
    simpa [inside, setLocal, sumAccumulator, comprehensionEnv] using getMax
  have innerAccumulator : inside sumAccumulator = some (number 0) := by simp [inside, setLocal]
  by_cases nonempty : 1 < limit
  · obtain ⟨extra, ran⟩ := loop (limit.toNat-1) 1 limit (by omega) maxIters heap inside 0 globals innerMax innerAccumulator
    refine ⟨extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range (name := "x") (filters := [tested]) (generators := [])
      (middle := heap) (afterStart := heap)
      (.cons Evaluates.constant (.cons (Evaluates.lookup getLimit) .nil)) rfl Evaluates.constant rfl
    have counted : (Lychrel.count limit.toNat maxIters.toNat : Int) =
        ((List.range' 1 (limit.toNat-1)).map (indicator maxIters)).sum :=
      Lychrel.count_eq_sum limit.toNat maxIters.toNat
    rw [counted]
    simpa only [inside, comprehensionFilters, sumBody, List.foldr_cons, List.foldr_nil, loopBody, Int.zero_add] using ran
  · have short : limit.toNat-1 = 0 := by omega
    refine ⟨[], ?_⟩
    simp only [Lychrel.count, short, List.range'_zero, List.filter_nil, List.length_nil, List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range (name := "x") (filters := [tested]) (generators := [])
      (middle := heap) (afterStart := heap)
      (.cons Evaluates.constant (.cons (Evaluates.lookup getLimit) .nil)) rfl Evaluates.constant rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup (by simp [setLocal]))

end naive

namespace naive_default
private abbrev program := P55Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)

/-- The ordinary reference adapter pins the original naive algorithm's iteration cap to fifty. -/
theorem result (limit : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive_default" [number limit] heap
      (number (Lychrel.count limit.toNat 50)) (heap ++ extra) globals := by
  obtain ⟨extra, ran⟩ := naive.result limit 50 heap globals
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) (.cons Evaluates.constant .nil)) ran

end naive_default
end data.«project-euler-statements».data.py.project_euler_statements.p55


namespace data.«project-euler-statements».data.py.project_euler_statements.p55
open FormalSW.PyAst
set_option Elab.async false

namespace naive

/-- The corrected original source terminates for every signed limit and iteration cap. -/
theorem «Returns» (limit maxIters : Int) :
    (HeapCalls.scalarFunction P55Ast.module "naive" [.int limit, .int maxIters]).Returns := by
  obtain ⟨extra, executed⟩ := result limit maxIters []
  exact executed.scalar_returns (values := [.int limit, .int maxIters])

theorem «Supported» (limit maxIters : Int) :
    (HeapCalls.scalarFunction P55Ast.module "naive" [.int limit, .int maxIters]).Supported :=
  («Returns» limit maxIters).supported

end naive

namespace naive_default

/-- The ordinary one-argument adapter has terminating execution for every signed limit. -/
theorem «Returns» (limit : Int) :
    (HeapCalls.scalarFunction P55Ast.module "naive_default" [.int limit]).Returns := by
  obtain ⟨extra, executed⟩ := result limit []
  exact executed.scalar_returns (values := [.int limit])

theorem «Supported» (limit : Int) :
    (HeapCalls.scalarFunction P55Ast.module "naive_default" [.int limit]).Supported :=
  («Returns» limit).supported

end naive_default
end data.«project-euler-statements».data.py.project_euler_statements.p55
