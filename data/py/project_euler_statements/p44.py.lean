import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p44.py.ast»
import lang.py.FormalSW.TruthCalls
import ProjectEulerSolutions.Lib.PentagonalDiscriminant
import ProjectEulerSolutions.Lib.PentagonalSearch
import ProjectEulerSolutions.Lib.HeapCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p44
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PentagonalDiscriminant
private abbrev program := P44Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

def polynomial (n : Int) : Int := n*(3*n-1)/2

theorem polynomial_nat (n : Nat) : polynomial n = (pentagonal n : Int) := by
  cases n with
  | zero => rfl
  | succ n => simp [polynomial, pentagonal, Int.natCast_sub (show 1 ≤ 3*(n+1) by omega)]

namespace pentagonal
/-- The source polynomial uses Python's exact integer floor division, including on negative inputs. -/
theorem result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "pentagonal" [number n] heap (number (polynomial n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (n*(3*n-1))) (bv := number 2) (middle := heap) (afterRight := heap)
  · apply Evaluates.binary (av := number n) (bv := number (3*n-1)) (middle := heap) (afterRight := heap)
      (Evaluates.lookup rfl)
    · exact Evaluates.binary (av := number (3*n)) (bv := number 1) (middle := heap) (afterRight := heap)
        (Evaluates.binary (av := number 3) (bv := number n) (middle := heap) (afterRight := heap)
          Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant rfl
    · rfl
  · exact Evaluates.constant
  · rfl
end pentagonal

def pentagonalTest (x : Int) : Bool := if x < 0 then false else exhaustive x.toNat

namespace is_pentagonal
private def condition : Expr := .compare (.call (.name "pentagonal") [.name "n"]) [(.eq, .name "x")]

private theorem loop (x first remaining stop : Nat) (length : first+remaining=stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getX : env "x" = some (number x)) :
    BlockReturns program env
      [.rangeStepLoop "n" first stop 1 (truthBody false condition) [], .return (.constant (.bool false))]
      heap (flag ((List.range' first remaining).any (fun n => decide (pentagonal n=x)))) heap := by
  induction remaining generalizing first env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ remaining ih =>
      let bound := setLocal env "n" (number first)
      have tested : Evaluates program bound condition heap (flag (decide (pentagonal first=x))) heap := by
        apply Evaluates.compare (middle := heap) (afterRight := heap) (av := number (pentagonal first)) (bv := number x)
        · apply Evaluates.call (values := [number first]) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil)
          simpa only [polynomial_nat] using pentagonal.result (first : Int) heap
        · exact Evaluates.lookup (by simpa [bound, setLocal] using getX)
        · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      rw [List.range'_succ, List.any_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      by_cases found : pentagonal first=x
      · simp only [found, decide_true, Bool.true_or]
        apply BlockReturns.branch (flag := true) tested
          (by simp [Mutable.truth, scalarTruth, found])
        exact BlockReturns.return_value Evaluates.constant
      · simp only [found, decide_false, Bool.false_or]
        apply BlockReturns.branch (flag := false) tested
          (by simp [Mutable.truth, scalarTruth, found])
        have rest := ih (first+1) (by omega) bound (by simpa [bound, setLocal] using getX)
        simpa only [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, Int.natCast_add, Int.natCast_one] using rest

/-- The exhaustive positive-index test terminates for every integer, preserving the caller heap. -/
theorem result (x : Int) (heap : Mutable.Heap) :
    ReturnsValue program "is_pentagonal" [number x] heap (flag (pentagonalTest x)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.truth_generator_range (universal := false) (values := [number 1, number (x+1)])
    (.cons Evaluates.constant (.cons (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)) rfl
  by_cases negative : x < 0
  · apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    simpa only [pentagonalTest, if_pos negative] using
      (BlockReturns.return_value (module := program) (heap := heap) (env := _)
        (Evaluates.constant (value := .bool false)))
  · lift x to Nat using (by omega : 0 ≤ x)
    let initial := functionEnv ((findFunctionIn program.body "is_pentagonal").getD ([], [])).1
      ((findFunctionIn program.body "is_pentagonal").getD ([], [])).2 [number x] []
    let inner := comprehensionTargetsEnv initial
      [(.name "n", .call (.name "range") [.constant (.int 1), .binOp (.name "x") .add (.constant (.int 1))], [])]
    have executed := loop x 1 x (x+1) (by omega) heap inner
      (by simp [inner, initial, comprehensionTargetsEnv, targetLocals]; rfl)
    simpa only [pentagonalTest, if_neg (by omega : ¬ (x : Int) < 0), Int.toNat_natCast,
      exhaustive, Int.natCast_add, Int.natCast_one] using executed

theorem «Returns» (x : Int) : (HeapCalls.scalarFunction program "is_pentagonal" [.int x]).Returns := by
  exact (result x []).scalar_returns

theorem «Supported» (x : Int) : (HeapCalls.scalarFunction program "is_pentagonal" [.int x]).Supported :=
  («Returns» x).supported
end is_pentagonal

namespace naive
open ProjectEulerSolutions.PentagonalSearch
private def decodedEnv (env : HeapCalls.Env) (j k : Nat) : HeapCalls.Env :=
  assignNames env ["pj", "pk"] [number (pentagonal j), number (pentagonal k)]
private def pairExpression : Expr := .tuple [.call (.name "pentagonal") [.name "j"], .call (.name "pentagonal") [.name "k"]]
private def sumExpression : Expr := .binOp (.name "pj") .add (.name "pk")
private def differenceExpression : Expr := .binOp (.name "pj") .sub (.name "pk")
private def predicate : Expr := .boolOp .and [.call (.name "is_pentagonal") [sumExpression], .call (.name "is_pentagonal") [differenceExpression]]
private def appendStatement : Stmt := .expr (.call (.attribute (.name "vals") "append") [differenceExpression])
def rowBody : List Stmt := [.assign [.tuple [.name "pj", .name "pk"]] pairExpression, .ifThen predicate [appendStatement] []]
def sourceRowBody : List Stmt :=
  match (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2).drop 1 with
  | .forIn _ _ [.forIn _ _ body _] _ :: _ => body
  | _ => []

theorem rowBody_source : rowBody = sourceRowBody := rfl

private theorem polynomial_call (name : String) (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getName : env name = some (number n)) :
    Evaluates program env (.call (.name "pentagonal") [.name name]) heap (number (pentagonal n)) heap := by
  exact Evaluates.call (.cons (Evaluates.lookup getName) .nil)
    (by simpa only [polynomial_nat] using pentagonal.result (n : Int) heap)

private theorem difference_result (j k : Nat) (bound : k ≤ j) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getPJ : env "pj" = some (number (pentagonal j))) (getPK : env "pk" = some (number (pentagonal k))) :
    Evaluates program env differenceExpression heap (number (difference j k)) heap := by
  exact Evaluates.binary (Evaluates.lookup getPJ) (Evaluates.lookup getPK)
    (by simp [Mutable.binary, scalarBinary, number, difference, Int.natCast_sub (strictMono.monotone bound)])

private theorem predicate_result (j k : Nat) (bound : k ≤ j) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getPJ : env "pj" = some (number (pentagonal j))) (getPK : env "pk" = some (number (pentagonal k))) :
    Evaluates program env predicate heap (flag (accepted j k)) heap := by
  have sumResult : Evaluates program env sumExpression heap (number (pentagonal j + pentagonal k)) heap :=
    Evaluates.binary (Evaluates.lookup getPJ) (Evaluates.lookup getPK) (by simp [Mutable.binary, scalarBinary, number])
  have sumTest : Evaluates program env (.call (.name "is_pentagonal") [sumExpression]) heap
      (flag (exhaustive (pentagonal j + pentagonal k))) heap := by
    apply Evaluates.call (.cons sumResult .nil)
    simpa only [pentagonalTest, if_neg (Int.not_lt.mpr (Int.natCast_nonneg _)), Int.toNat_natCast] using
      is_pentagonal.result ((pentagonal j + pentagonal k : Nat) : Int) heap
  have diffTest : Evaluates program env (.call (.name "is_pentagonal") [differenceExpression]) heap
      (flag (exhaustive (difference j k))) heap := by
    apply Evaluates.call (.cons (difference_result j k bound heap env getPJ getPK) .nil)
    simpa only [pentagonalTest, if_neg (Int.not_lt.mpr (Int.natCast_nonneg _)), Int.toNat_natCast] using
      is_pentagonal.result ((difference j k : Nat) : Int) heap
  cases keep : exhaustive (pentagonal j + pentagonal k) with
  | false =>
      simp only [accepted, keep, Bool.false_and]
      exact Evaluates.boolean_stop (flag := false) (by simpa only [keep] using sumTest) rfl rfl
  | true =>
      simp only [accepted, keep, Bool.true_and]
      exact Evaluates.boolean_next (flag := true) (by simpa only [keep] using sumTest) rfl rfl
        (Evaluates.boolean_last diffTest rfl)

/-- One source pair allocates its tuple and appends exactly its accepted positive-index difference. -/
theorem row (j k : Nat) (bound : k < j) (base : Mutable.Heap) (values : List Nat) (garbage : Mutable.Heap)
    (env : HeapCalls.Env) (getJ : env "j" = some (number j)) (getK : env "k" = some (number k))
    (getVals : env "vals" = some (.ref base.length)) :
    BlockContinues program env rowBody (ProjectEulerSolutions.HeapCollection.working base (values.map fun n : Nat => number n) garbage)
      (decodedEnv env j k)
      (ProjectEulerSolutions.HeapCollection.working base
        ((values ++ (if accepted j k then [difference j k] else [])).map fun n : Nat => number n)
        (garbage ++ [.tuple [number (pentagonal j), number (pentagonal k)]])) := by
  let initial := ProjectEulerSolutions.HeapCollection.working base (values.map fun n : Nat => number n) garbage
  let tuple := Mutable.Object.tuple [number (pentagonal j), number (pentagonal k)]
  let afterTuple := ProjectEulerSolutions.HeapCollection.working base (values.map fun n : Nat => number n) (garbage ++ [tuple])
  let decoded := decodedEnv env j k
  have decode : BlockContinues program env [.assign [.tuple [.name "pj", .name "pk"]] pairExpression] initial decoded afterTuple := by
    apply BlockContinues.unpack (names := ["pj", "pk"]) (items := [number (pentagonal j), number (pentagonal k)]) rfl
      (Evaluates.tuple (.cons (polynomial_call "j" j initial env getJ) (.cons (polynomial_call "k" k initial env getK) .nil)) (by simp))
      (by simp [Mutable.sequence, initial, afterTuple, ProjectEulerSolutions.HeapCollection.working, tuple]) rfl
  have getPJ : decoded "pj" = some (number (pentagonal j)) := by simp [decoded, decodedEnv, assignNames, setLocal]
  have getPK : decoded "pk" = some (number (pentagonal k)) := by simp [decoded, decodedEnv, assignNames, setLocal]
  have tested := predicate_result j k (by omega) afterTuple decoded getPJ getPK
  cases keep : accepted j k with
  | false =>
      simp only [Bool.false_eq_true, if_false, List.append_nil]
      apply decode.append
      exact BlockContinues.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, keep]) .nil
  | true =>
      simp only [if_true]
      apply decode.append
      apply BlockContinues.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, keep])
      have appended := Evaluates.append (base := .name "vals") (Evaluates.lookup (by simpa [decoded, decodedEnv, assignNames, setLocal] using getVals))
        (ProjectEulerSolutions.HeapCollection.found base (values.map fun n : Nat => number n) (garbage ++ [tuple]))
        (difference_result j k (by omega) afterTuple decoded getPJ getPK)
        (ProjectEulerSolutions.HeapCollection.found base (values.map fun n : Nat => number n) (garbage ++ [tuple]))
      have stored := BlockContinues.discard appended
      simpa only [afterTuple, ProjectEulerSolutions.HeapCollection.store, List.map_append, List.map_cons, List.map_nil] using stored

private def collected (j first count : Nat) : List Nat :=
  ((List.range' first count).filter (accepted j)).map (difference j)
private theorem collected_cons (j first count : Nat) :
    collected j first (count+1) = (if accepted j first then [difference j first] else []) ++ collected j (first+1) count := by
  cases keep : accepted j first <;> simp [collected, List.range'_succ, keep]

private theorem decoded_other (env : HeapCalls.Env) (j k : Nat) (name : String)
    (unrelated : name ∉ ["pj", "pk"]) : decodedEnv env j k name = env name := by
  have npj : name ≠ "pj" := by intro equal; subst name; simp at unrelated
  have npk : name ≠ "pk" := by intro equal; subst name; simp at unrelated
  simp [decodedEnv, assignNames, setLocal, npj, npk]

/-- The reference's inner loop collects all smaller positive indices in ascending order. -/
theorem range_result (j first count : Nat) (equation : first+count=j) (positive : 1 ≤ first)
    (base : Mutable.Heap) (values : List Nat) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (getJ : env "j" = some (number j)) (getVals : env "vals" = some (.ref base.length)) :
    ∃ finalGarbage finalEnv, BlockContinues program env [.rangeStepLoop "k" first j 1 rowBody []]
        (ProjectEulerSolutions.HeapCollection.working base (values.map fun n : Nat => number n) garbage) finalEnv
        (ProjectEulerSolutions.HeapCollection.working base ((values ++ collected j first count).map fun n : Nat => number n) finalGarbage) ∧
      (∀ name, name ∉ ["k", "pj", "pk"] → finalEnv name = env name) := by
  induction count generalizing first values garbage env with
  | zero =>
      refine ⟨garbage, env, ?_, ?_⟩
      · simpa only [collected, List.range'_zero, List.filter_nil, List.map_nil, List.append_nil] using
          (BlockContinues.range_done (module := program) (env := env)
            (by simp [Calls.rangeContinues]; omega) BlockContinues.nil)
      · intros; rfl
  | succ count ih =>
      let bound := setLocal env "k" (number first)
      let nextValues := values ++ (if accepted j first then [difference j first] else [])
      let nextGarbage := garbage ++ [.tuple [number (pentagonal j), number (pentagonal first)]]
      have step := row j first (by omega) base values garbage bound
        (by simpa [bound, setLocal] using getJ) (by simp [bound, setLocal]) (by simpa [bound, setLocal] using getVals)
      obtain ⟨finalGarbage, finalEnv, executed, untouched⟩ := ih (first+1) (by omega) (by omega)
        nextValues nextGarbage (decodedEnv bound j first)
          (by rw [decoded_other _ _ _ "j" (by decide)]; simpa [bound, setLocal] using getJ)
          (by rw [decoded_other _ _ _ "vals" (by decide)]; simpa [bound, setLocal] using getVals)
      refine ⟨finalGarbage, finalEnv, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl rowBody = false from rfl,
          Bool.false_eq_true, if_false, collected_cons, nextValues, List.append_assoc,
          Int.natCast_add, Int.natCast_one] using step.append executed
      · intro name unrelated
        have nk : name ≠ "k" := by intro equal; subst name; simp at unrelated
        have others : name ∉ ["pj", "pk"] := fun member => unrelated (List.mem_cons_of_mem _ member)
        rw [untouched name unrelated, decoded_other _ _ _ name others]
        simp [bound, setLocal, nk]

private def innerLoop : List Stmt := [.forIn (.name "k") (.call (.name "range") [.constant (.int 1), .name "j"]) rowBody []]
private def collectedRows (indices : List Nat) : List Nat := indices.flatMap fun j => rowValues j (j-1)

/-- The complete pair enumeration retains the caller heap and the exact list consumed by the minimum loop. -/
theorem outer_result (first count stop : Nat) (equation : first+count=stop) (positive : 1 ≤ first)
    (base : Mutable.Heap) (values : List Nat) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (getVals : env "vals" = some (.ref base.length)) :
    ∃ finalGarbage finalEnv, BlockContinues program env [.rangeStepLoop "j" first stop 1 innerLoop []]
        (ProjectEulerSolutions.HeapCollection.working base (values.map fun n : Nat => number n) garbage) finalEnv
        (ProjectEulerSolutions.HeapCollection.working base ((values ++ collectedRows (List.range' first count)).map fun n : Nat => number n) finalGarbage) ∧
      (∀ name, name ∉ ["j", "k", "pj", "pk"] → finalEnv name = env name) := by
  induction count generalizing first values garbage env with
  | zero =>
      refine ⟨garbage, env, ?_, ?_⟩
      · simpa only [List.range'_zero, collectedRows, List.flatMap_nil, List.append_nil] using
          (BlockContinues.range_done (module := program) (env := env)
            (by simp [Calls.rangeContinues]; omega) BlockContinues.nil)
      · intros; rfl
  | succ count ih =>
      let bound := setLocal env "j" (number first)
      obtain ⟨nextGarbage, middleEnv, iteration, same⟩ := range_result first 1 (first-1) (by omega) (by omega)
        base values garbage bound (by simp [bound, setLocal]) (by simpa [bound, setLocal] using getVals)
      have loop : BlockContinues program bound innerLoop
          (ProjectEulerSolutions.HeapCollection.working base (values.map fun n : Nat => number n) garbage) middleEnv
          (ProjectEulerSolutions.HeapCollection.working base ((values ++ rowValues first (first-1)).map fun n : Nat => number n) nextGarbage) := by
        exact BlockContinues.for_range (values := [number 1, number first]) (.cons Evaluates.constant (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil)) rfl iteration
      obtain ⟨finalGarbage, finalEnv, executed, untouched⟩ := ih (first+1) (by omega) (by omega)
        (values ++ rowValues first (first-1)) nextGarbage middleEnv
          (by rw [same "vals" (by decide)]; simpa [bound, setLocal] using getVals)
      refine ⟨finalGarbage, finalEnv, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl innerLoop = false from rfl,
          Bool.false_eq_true, if_false, List.range'_succ, collectedRows, List.flatMap_cons,
          List.append_assoc, Int.natCast_add, Int.natCast_one] using loop.append executed
      · intro name unrelated
        have nj : name ≠ "j" := by intro equal; subst name; simp at unrelated
        have others : name ∉ ["k", "pj", "pk"] := fun member => unrelated (List.mem_cons_of_mem _ member)
        rw [untouched name unrelated, same name others]
        simp [bound, setLocal, nj]

private def minBody : List Stmt := [.assign [.name "acc"] (.builtinCall .min [.name "acc", .name "v"])]

/-- The separate source minimum pass uses its explicit sentinel and leaves the collected list unchanged. -/
theorem minimum_result (all : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (all.map fun n : Nat => number n)))
    (remaining : List Nat) (position : Nat) (split : all.drop position = remaining)
    (initial : Nat) (env : HeapCalls.Env) (getAcc : env "acc" = some (number initial)) :
    ∃ finalEnv, BlockContinues program env [.sequenceStepLoop "v" (.ref address) position minBody []] heap finalEnv heap ∧
      finalEnv "acc" = some (number ((remaining.foldl Nat.min initial : Nat) : Int)) := by
  have sequence : Mutable.sequence (.ref address) heap = some (.ok (all.map fun n : Nat => number n), heap) := by
    simp [Mutable.sequence, found]
  induction remaining generalizing position initial env with
  | nil =>
      refine ⟨env, ?_, getAcc⟩
      exact BlockContinues.sequence_done sequence
        (by have empty := congrArg List.head? split; simpa [List.head?_drop] using empty) .nil
  | cons first rest ih =>
      let bound := setLocal env "v" (number first)
      let ready := setLocal bound "acc" (number (Nat.min initial first))
      have step : BlockContinues program bound minBody heap ready heap := by
        apply BlockContinues.assign
        apply Evaluates.builtin (values := [number initial, number first])
          (.cons (Evaluates.lookup (by simpa [bound, setLocal] using getAcc)) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil))
        by_cases smaller : first < initial
        · have order : first ≤ initial := by omega
          simp [primitive, Calls.positionalMinimum, Calls.minimumFrom, scalarCompare, evalCmpOp, number,
            smaller, min_eq_right order, scalarResult]
        · have order : initial ≤ first := by omega
          simp [primitive, Calls.positionalMinimum, Calls.minimumFrom, scalarCompare, evalCmpOp, number,
            smaller, min_eq_left order, scalarResult]
      obtain ⟨finalEnv, executed, acc⟩ := ih (position+1) (by simp [List.drop_add_one_eq_tail_drop, split])
        (Nat.min initial first) ready (by simp [ready, setLocal])
      refine ⟨finalEnv, ?_, acc⟩
      have selected : all[position]? = some first := by
        simpa only [split, List.head?_cons] using (List.head?_drop (l := all) (i := position)).symm
      apply BlockContinues.sequence_step (source := .ref address) (value := number first) sequence (by simp [selected])
      simpa only [Calls.loopContinuation, show Calls.loopControl minBody = false from rfl,
        Bool.false_eq_true, if_false] using step.append executed

private def pairsLoop : List Stmt := [.forIn (.name "j")
  (.call (.name "range") [.constant (.int 1), .binOp (.name "limit") .add (.constant (.int 1))]) innerLoop []]

/-- Negative limits skip the pair enumeration; nonnegative ones enumerate precisely the bounded search. -/
theorem enumerate (limit : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) (getVals : env "vals" = some (.ref heap.length)) :
    ∃ garbage finalEnv, BlockContinues program env pairsLoop
        (ProjectEulerSolutions.HeapCollection.working heap [] []) finalEnv
        (ProjectEulerSolutions.HeapCollection.working heap ((values limit.toNat).map fun n : Nat => number n) garbage) ∧
      finalEnv "vals" = some (.ref heap.length) := by
  have arguments : Evaluates.Arguments program env [.constant (.int 1), .binOp (.name "limit") .add (.constant (.int 1))]
      (ProjectEulerSolutions.HeapCollection.working heap [] []) [number 1, number (limit+1)]
      (ProjectEulerSolutions.HeapCollection.working heap [] []) :=
    .cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup getLimit) Evaluates.constant rfl) .nil)
  by_cases negative : limit < 0
  · refine ⟨[], env, ?_, getVals⟩
    apply BlockContinues.for_range arguments rfl
    have empty : values limit.toNat = [] := by
      have zero : limit.toNat = 0 := by omega
      simp only [zero, values, List.range'_zero, List.flatMap_nil]
    rw [empty]
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  · lift limit to Nat using (by omega : 0 ≤ limit)
    obtain ⟨garbage, finalEnv, executed, untouched⟩ := outer_result 1 limit (limit+1) (by omega) (by omega)
      heap [] [] env getVals
    refine ⟨garbage, finalEnv, ?_, ?_⟩
    · apply BlockContinues.for_range arguments rfl
      simpa only [Int.toNat_natCast, collectedRows, values, List.nil_append, Int.natCast_add, Int.natCast_one] using executed
    · rw [untouched "vals" (by decide)]
      exact getVals

/-- The corrected brute-force reference returns the same capped minimum, for every integer limit. -/
theorem result (limit : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap (number (search limit.toNat)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let ready := setLocal initial "vals" (.ref heap.length)
  obtain ⟨garbage, collectedEnv, collected, getVals⟩ := enumerate limit heap ready (by simp [ready, initial, setLocal]; rfl) (by simp [ready, setLocal])
  let current := ProjectEulerSolutions.HeapCollection.working heap ((values limit.toNat).map fun n : Nat => number n) garbage
  let zeroed := setLocal collectedEnv "acc" (number cap)
  obtain ⟨finalEnv, executed, acc⟩ := minimum_result (values limit.toNat) current heap.length
    (ProjectEulerSolutions.HeapCollection.found _ _ _) (values limit.toNat) 0 rfl cap zeroed (by simp [zeroed, setLocal])
  have initialized : BlockContinues program collectedEnv [.assign [.name "acc"] (.binOp (.constant (.int 10)) .pow (.constant (.int 30)))]
      current zeroed current :=
    BlockContinues.assign (Evaluates.binary Evaluates.constant Evaluates.constant rfl)
  have loop : BlockContinues program zeroed [.forIn (.name "v") (.name "vals") minBody []] current finalEnv current :=
    BlockContinues.for_sequence (value := .ref heap.length) (items := (values limit.toNat).map fun n : Nat => number n)
      (by intros; simp) (Evaluates.lookup (by simpa [zeroed, setLocal] using getVals))
      (by simp [Mutable.sequence, current, ProjectEulerSolutions.HeapCollection.found]) executed
  refine ⟨.list ((values limit.toNat).map fun n : Nat => number n) :: garbage, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply ((collected.append initialized).append loop).returns
  exact BlockReturns.return_value (Evaluates.lookup acc)

theorem «Returns» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  obtain ⟨_, returned⟩ := result limit []
  exact returned.scalar_returns

theorem «Supported» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  («Returns» limit).supported

end naive

end data.«project-euler-statements».data.py.project_euler_statements.p44
