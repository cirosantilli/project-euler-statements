import ProjectEulerSolutions.Lib.SpiralRowCertificates.All
import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p58.py.ast»
import FormalSW
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.SpiralPrimes

namespace data.«project-euler-statements».data.py.project_euler_statements.p58
open FormalSW.PyAst FormalSW.PyAst.Calls
set_option Elab.async false

private abbrev program := P58Ast.module

/-- The actual source computes the diagonal total as an integer polynomial, including signed inputs. -/
theorem diag_total.result (k : Int) :
    ReturnsValue program "diag_total" [.int k] (.int (4 * k + 1)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .int (2 * k + 1))
  · exact Evaluates.binary
      (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant rfl
  · apply BlockReturns.return_value
    apply Evaluates.binary
      (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant
    simp [scalarBinary]
    omega

theorem diag_total.«Returns» (k : Int) :
    (FormalSW.PyAst.scalarFunction program "diag_total" [.int k]).Returns :=
  ⟨.int (2 * (2 * k + 1) - 1), .next rfl (.done rfl)⟩

/-- The same source helper leaves both heap and cache unchanged inside the reference scan. -/
theorem diag_total.memo_result (k : Int) (heap : Mutable.Heap) (spec : HeapMemoCalls.Specification) :
    HeapMemoCalls.ReturnsRel program spec "diag_total" [.scalar (.int k)] heap
      (fun value after => value = .scalar (.int (4 * k + 1)) ∧ after = heap) := by
  apply HeapMemoCalls.BlockReturnsRel.function (by decide) rfl rfl
  apply HeapMemoCalls.BlockReturnsRel.assign
    (HeapMemoCalls.Evaluates.binary (value := .scalar (.int (2 * k + 1)))
      (HeapMemoCalls.Evaluates.binary HeapMemoCalls.Evaluates.constant
        (HeapMemoCalls.Evaluates.lookup rfl) rfl) HeapMemoCalls.Evaluates.constant rfl).rel
  rintro value middle ⟨rfl, rfl⟩
  apply HeapMemoCalls.BlockReturnsRel.return_value
  apply (HeapMemoCalls.Evaluates.binary (value := .scalar (.int (4 * k + 1)))
    (HeapMemoCalls.Evaluates.binary HeapMemoCalls.Evaluates.constant
      (HeapMemoCalls.Evaluates.lookup rfl) rfl) HeapMemoCalls.Evaluates.constant ?_).rel
  simp [Mutable.binary, scalarBinary]
  omega

end data.«project-euler-statements».data.py.project_euler_statements.p58

namespace data.«project-euler-statements».data.py.project_euler_statements.p58.diag_prime_count
open FormalSW.PyAst FormalSW.PyAst.HeapMemoCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev source := P58Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def encode (items : List Nat) : List Mutable.Value := items.map fun item => number item

/-- Cached diagonal counts are scalar values independent of heap allocation. -/
def spec (_heap : Mutable.Heap) (key : MemoCalls.Key) (value : Mutable.Value) : Prop :=
  ∃ layer : Nat, key = ⟨"diag_prime_count", [layer]⟩ ∧ value = number (SpiralPrimes.count layer)

private theorem preserves (before after : Mutable.Heap) : Cache.Preserves spec before after :=
  fun _ valid => valid

private theorem common_extension : HeapCalls.Extends source CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  have extension : Calls.Extends { body := source.body.take 6 ++ CommonAst.module.body } CommonAst.module := by
    apply Calls.Extends.prepend
    · intro name member
      change name ∈ ["diag_prime_count", "diag_total", "ratio_below", "naive", "naive_default"] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    · intro name member
      change name ∈ ([] : List String) at member
      simp at member
  exact ⟨extension.functions, extension.libraries⟩

private theorem common_disjoint : CacheDisjoint source CommonAst.module := by
  intro name cached
  change name ∈ ["diag_prime_count"] at cached
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cached
  subst name
  exact ⟨rfl, rfl, rfl⟩

private theorem prime_call (item : Nat) (heap : Mutable.Heap) :
    ReturnsValue source spec "is_prime" [number item] heap (flag (decide (Nat.Prime item))) heap :=
  ReturnsValue.from_heap common_extension common_disjoint
    (common.is_prime.heap_result item heap) Cache.Preserves.refl

private theorem found_append {heap : Mutable.Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem list_sequence {heap : Mutable.Heap} {address : Nat} {items : List Mutable.Value}
    (found : heap[address]? = some (.list items)) :
    Mutable.sequence (.ref address) heap = some (.ok items, heap) := by
  simp [Mutable.sequence, found]

private abbrev primeTest : Expr := .call (.name "is_prime") [.name "c"]
private abbrev filteredRow : List Stmt :=
  [.ifThen primeTest
    [.assign [.name HeapCalls.sumAccumulator]
      (.binOp (.name HeapCalls.sumAccumulator) .add (.constant (.int 1)))] []]
private abbrev filteredTail (address position : Nat) : List Stmt :=
  [.sequenceStepLoop "c" (.ref address) position filteredRow [], .return (.name HeapCalls.sumAccumulator)]

/-- The filter calls the actual linked trial-division helper on each current item. -/
private theorem filtered_loop (remaining : List Nat) (before : List Nat)
    (env : Mutable.Env) (heap : Mutable.Heap) (address : Nat) (running : Int)
    (found : heap[address]? = some (.list (encode (before ++ remaining))))
    (getSum : env HeapCalls.sumAccumulator = some (number running)) :
    BlockReturnsRel source spec env (filteredTail address before.length) heap
      (fun value after => value = number (running + (SpiralPrimes.primeCount remaining : Int)) ∧ after = heap) := by
  induction remaining generalizing before env running with
  | nil =>
      apply BlockReturnsRel.sequence_done (items := encode (before ++ []))
        (by simpa only [HeapCalls.sequenceValue] using list_sequence found)
        (by simp [encode])
      apply BlockReturnsRel.return_value
      apply EvaluatesRel.lookup getSum
      simp [SpiralPrimes.primeCount]
  | cons head rest ih =>
      apply BlockReturnsRel.sequence_step (value := number head) (items := encode (before ++ head :: rest))
        (by simpa only [HeapCalls.sequenceValue] using list_sequence found)
        (by simp [encode, List.map_append])
      apply BlockReturnsRel.branch
        (Evaluates.call (.cons (Evaluates.lookup (value := number head) (by simp [HeapCalls.setLocal])) .nil)
          (prime_call head heap)).rel
      rintro tested middle ⟨equalValue, equalHeap⟩
      subst tested
      subst middle
      refine ⟨decide (Nat.Prime head), rfl, ?_⟩
      have nextFound : heap[address]? = some (.list (encode ((before ++ [head]) ++ rest))) := by
        simpa only [List.append_assoc, List.singleton_append] using found
      by_cases prime : Nat.Prime head
      · simp only [prime, decide_true, ite_true]
        apply BlockReturnsRel.assign
          (Evaluates.binary
            (Evaluates.lookup (value := number running) (by simpa [HeapCalls.setLocal] using getSum))
            Evaluates.constant rfl).rel
        rintro updated after ⟨equalValue, equalHeap⟩
        subst updated
        subst after
        have loop := ih (before ++ [head])
          (HeapCalls.setLocal (HeapCalls.setLocal env "c" (number head)) HeapCalls.sumAccumulator (number (running + 1)))
          (running + 1) nextFound (by simp [HeapCalls.setLocal])
        apply BlockReturnsRel.consequence (pre := fun value after =>
          value = number (running + 1 + (SpiralPrimes.primeCount rest : Int)) ∧ after = heap)
        · simpa [filteredTail, filteredRow, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using loop
        · rintro value after ⟨equal, same⟩
          refine ⟨equal.trans (congrArg number ?_), same⟩
          simp [SpiralPrimes.primeCount, prime]
          omega
      · simp only [prime, decide_false]
        have loop := ih (before ++ [head]) (HeapCalls.setLocal env "c" (number head)) running
          nextFound (by simpa [HeapCalls.setLocal] using getSum)
        apply BlockReturnsRel.consequence (pre := fun value after =>
          value = number (running + (SpiralPrimes.primeCount rest : Int)) ∧ after = heap)
        · simpa [filteredTail, filteredRow, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using loop
        · rintro value after ⟨equal, same⟩
          refine ⟨equal.trans (congrArg number ?_), same⟩
          simp [SpiralPrimes.primeCount, prime]

private theorem filtered_sum (items : List Nat) (env : Mutable.Env) (heap : Mutable.Heap) (address : Nat)
    (getCorners : env "corners" = some (.ref address))
    (found : heap[address]? = some (.list (encode items))) :
    EvaluatesRel source spec env
      (.sumGenerator (.constant (.int 1)) [("c", .name "corners", [primeTest])] (.constant (.int 0))) heap
      (fun value after => value = number (SpiralPrimes.primeCount items) ∧ after = heap) := by
  apply EvaluatesRel.sum_generator_sequence
    (iterablePost := fun value after => value = .ref address ∧ after = heap)
    (startPost := fun _ middle value after => value = number 0 ∧ after = middle)
  · exact (Evaluates.lookup getCorners).rel
  · intro bounds equal
    cases equal
  · rintro value middle ⟨equalValue, equalHeap⟩
    subst value
    subst middle
    exact ⟨encode items, list_sequence found⟩
  · intro value middle _
    exact EvaluatesRel.constant ⟨rfl, rfl⟩
  · rintro value middle initial after ⟨equalValue, equalHeap⟩ ⟨equalInitial, equalAfter⟩
    subst value
    subst middle
    subst initial
    subst after
    refine ⟨rfl, ?_⟩
    simpa [filteredTail, filteredRow] using
      filtered_loop items [] _ heap address 0 found (by simp [HeapCalls.setLocal])

private def signedSide (layer : Nat) : Int := 2 * (layer : Int) + 1
private def signedSquare (layer : Nat) : Int := signedSide layer ^ 2
private def signedStep (layer : Nat) : Int := signedSide layer - 1

private theorem square_cast (layer : Nat) : (SpiralPrimes.square layer : Int) = signedSquare layer := by
  simp [SpiralPrimes.square, SpiralPrimes.side, signedSquare, signedSide]

private theorem step_cast (layer : Nat) : (SpiralPrimes.step layer : Int) = signedStep layer := by
  simp [SpiralPrimes.step, signedStep, signedSide]

private theorem corner_cast (layer offset : Nat) (bound : offset ≤ 3) :
    (SpiralPrimes.corner layer offset : Int) = signedSquare layer - offset * signedStep layer := by
  rw [SpiralPrimes.corner, Nat.cast_sub (Nat.le_of_lt (SpiralPrimes.corner_offset_lt_square layer offset bound)),
    Nat.cast_mul, square_cast, step_cast]

private theorem encoded_corners (layer : Nat) : encode (SpiralPrimes.allCorners layer) =
    [number (signedSquare layer), number (signedSquare layer - signedStep layer),
      number (signedSquare layer - 2 * signedStep layer), number (signedSquare layer - 3 * signedStep layer)] := by
  simp [encode, SpiralPrimes.allCorners, SpiralPrimes.corners, square_cast,
    corner_cast layer 1 (by decide), corner_cast layer 2 (by decide), corner_cast layer 3 (by decide)]

private abbrev cornerExpression : Expr :=
  .list [.name "sq", .binOp (.name "sq") .sub (.name "step"),
    .binOp (.name "sq") .sub (.binOp (.constant (.int 2)) .mult (.name "step")),
    .binOp (.name "sq") .sub (.binOp (.constant (.int 3)) .mult (.name "step"))]

private theorem corner_list (layer : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getSquare : env "sq" = some (number (signedSquare layer)))
    (getStep : env "step" = some (number (signedStep layer))) :
    Evaluates source spec env cornerExpression heap (.ref heap.length)
      (heap ++ [.list (encode (SpiralPrimes.allCorners layer))]) := by
  simpa only [encoded_corners] using
    (Evaluates.list (.cons (Evaluates.lookup getSquare) (.cons
      (Evaluates.binary (Evaluates.lookup getSquare) (Evaluates.lookup getStep) rfl) (.cons
      (Evaluates.binary (Evaluates.lookup getSquare)
        (Evaluates.binary (Evaluates.constant (value := .int 2)) (Evaluates.lookup getStep) rfl) rfl) (.cons
      (Evaluates.binary (Evaluates.lookup getSquare)
        (Evaluates.binary (Evaluates.constant (value := .int 3)) (Evaluates.lookup getStep) rfl) rfl) .nil)))) (preserves heap _))

private abbrev recursiveExpression : Expr :=
  .call (.name "diag_prime_count") [.binOp (.name "k") .sub (.constant (.int 1))]
private abbrev countSum : Expr :=
  .sumGenerator (.constant (.int 1)) [("c", .name "corners", [primeTest])] (.constant (.int 0))

private theorem finish (layer : Nat) (env : Mutable.Env) (heap : Mutable.Heap) (address : Nat)
    (getLayer : env "k" = some (number (layer + 1)))
    (getCorners : env "corners" = some (.ref address))
    (found : heap[address]? = some (.list (encode (SpiralPrimes.allCorners (layer + 1)))))
    (recursive : ∀ heap, ReturnsRel source spec "diag_prime_count" [number layer] heap
      (fun value after => value = number (SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra)) :
    BlockReturnsRel source spec env [.return (.binOp recursiveExpression .add countSum)] heap
      (fun value after => value = number (SpiralPrimes.count (layer + 1)) ∧ ∃ extra, after = heap ++ extra) := by
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.binary
    (leftPost := fun value after => value = number (SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra)
    (rightPost := fun _ middle value after => value = number (SpiralPrimes.primeCount (SpiralPrimes.allCorners (layer + 1))) ∧ after = middle)
  · apply EvaluatesRel.call (ArgumentsRel.fixed (.cons
      (Evaluates.binary (value := number layer) (finalHeap := heap) (Evaluates.lookup getLayer) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary])) .nil))
    rintro values middle ⟨equalValues, equalHeap⟩
    subst values
    subst middle
    exact recursive heap
  · rintro left middle ⟨equalLeft, extra, equalHeap⟩
    subst left
    subst middle
    exact filtered_sum _ env (heap ++ extra) address getCorners (found_append found extra)
  · rintro left middle right after ⟨equalLeft, extra, equalHeap⟩ ⟨equalRight, equalAfter⟩
    subst left
    subst middle
    subst right
    subst after
    have arithmetic : (SpiralPrimes.count layer : Int) +
        SpiralPrimes.primeCount (SpiralPrimes.allCorners (layer + 1)) = SpiralPrimes.count (layer + 1) := by
      simp [SpiralPrimes.count_succ, SpiralPrimes.allCorners_primeCount]
    refine ⟨number (SpiralPrimes.count (layer + 1)), heap ++ extra, ?_, Cache.Preserves.refl, rfl, extra, rfl⟩
    simpa only [arithmetic] using
      (show Mutable.binary .add (number (SpiralPrimes.count layer))
        (number (SpiralPrimes.primeCount (SpiralPrimes.allCorners (layer + 1)))) (heap ++ extra) =
        some (.ok (number ((SpiralPrimes.count layer : Int) + SpiralPrimes.primeCount (SpiralPrimes.allCorners (layer + 1)))), heap ++ extra) from rfl)

private theorem hit (layer : Nat) (heap : Mutable.Heap) (value : Mutable.Value)
    (valid : spec heap ⟨"diag_prime_count", [layer]⟩ value) :
    value = number (SpiralPrimes.count layer) ∧ ∃ extra, heap = heap ++ extra := by
  obtain ⟨other, equalKey, equalValue⟩ := valid
  have equalCast : (layer : Int) = (other : Int) := by simpa [MemoCalls.Key.mk.injEq] using equalKey
  have equalLayer : layer = other := by exact_mod_cast equalCast
  subst other
  exact ⟨equalValue, [], by simp⟩

/-- The actual recursive cached source computes every finite spiral before. -/
theorem result (layer : Nat) (heap : Mutable.Heap) :
    ReturnsRel source spec "diag_prime_count" [number layer] heap
      (fun value after => value = number (SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra) := by
  induction layer generalizing heap with
  | zero =>
      apply BlockReturnsRel.memoized_function (values := [0]) (by decide) rfl rfl
      · apply BlockReturnsRel.consequence (pre := fun value after => value = number (SpiralPrimes.count 0) ∧ ∃ extra, after = heap ++ extra)
        · apply BlockReturnsRel.branch
            (Evaluates.compare (value := flag true) (Evaluates.lookup (value := number 0) rfl) Evaluates.constant rfl).rel
          rintro value middle ⟨equalValue, equalHeap⟩
          subst value
          subst middle
          refine ⟨true, rfl, ?_⟩
          exact BlockReturnsRel.return_value (EvaluatesRel.constant ⟨rfl, [], by simp⟩)
        · rintro value after ⟨equalValue, framed⟩
          exact ⟨⟨equalValue, framed⟩, 0, rfl, equalValue⟩
      · exact hit 0 heap
  | succ layer ih =>
      apply BlockReturnsRel.memoized_function (values := [layer + 1]) (by decide) rfl rfl
      · apply BlockReturnsRel.consequence (pre := fun value after => value = number (SpiralPrimes.count (layer + 1)) ∧ ∃ extra, after = heap ++ extra)
        · apply BlockReturnsRel.branch
          · apply (Evaluates.compare (value := flag false)
              (Evaluates.lookup (value := number (layer + 1)) rfl) Evaluates.constant ?_).rel
            simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
            omega
          · rintro value middle ⟨equalValue, equalHeap⟩
            subst value
            subst middle
            refine ⟨false, rfl, ?_⟩
            apply BlockReturnsRel.assign
              (Evaluates.binary (value := number (signedSide (layer + 1)))
                (Evaluates.binary Evaluates.constant (Evaluates.lookup (value := number (layer + 1)) rfl) rfl)
                Evaluates.constant rfl).rel
            rintro value middle ⟨equalValue, equalHeap⟩
            subst value
            subst middle
            apply BlockReturnsRel.assign
              (Evaluates.binary (value := number (signedSquare (layer + 1)))
                (Evaluates.lookup (value := number (signedSide (layer + 1))) rfl) Evaluates.constant rfl).rel
            rintro value middle ⟨equalValue, equalHeap⟩
            subst value
            subst middle
            apply BlockReturnsRel.assign
              (Evaluates.binary (value := number (signedStep (layer + 1)))
                (Evaluates.lookup (value := number (signedSide (layer + 1))) rfl) Evaluates.constant rfl).rel
            rintro value middle ⟨equalValue, equalHeap⟩
            subst value
            subst middle
            apply BlockReturnsRel.assign (corner_list (layer + 1) _ heap (by rfl) (by rfl)).rel
            rintro value middle ⟨equalValue, equalHeap⟩
            subst value
            subst middle
            apply BlockReturnsRel.consequence (pre := fun value after =>
              value = number (SpiralPrimes.count (layer + 1)) ∧
              ∃ extra, after = (heap ++ [.list (encode (SpiralPrimes.allCorners (layer + 1)))]) ++ extra)
            · apply finish layer
              · rfl
              · rfl
              · simp
              · exact ih
            · rintro value after ⟨equalValue, extra, equalHeap⟩
              refine ⟨equalValue, [.list (encode (SpiralPrimes.allCorners (layer + 1)))] ++ extra, ?_⟩
              simpa only [List.append_assoc] using equalHeap
        · rintro value after ⟨equalValue, framed⟩
          exact ⟨⟨equalValue, framed⟩, layer + 1, rfl, equalValue⟩
      · exact hit (layer + 1) heap

end data.«project-euler-statements».data.py.project_euler_statements.p58.diag_prime_count

namespace data.«project-euler-statements».data.py.project_euler_statements.p58
open FormalSW.PyAst FormalSW.PyAst.HeapMemoCalls
open ProjectEulerSolutions
set_option Elab.async false

namespace ratio_below
private abbrev source := P58Ast.module
private abbrev cacheSpec := diag_prime_count.spec
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

private theorem count_call (layer : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number layer)) :
    EvaluatesRel source cacheSpec env (.call (.name "diag_prime_count") [.name "k"]) heap
      (fun value after => value = number (SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra) := by
  apply EvaluatesRel.call (ArgumentsRel.fixed (.cons (Evaluates.lookup getLayer) .nil))
  rintro values middle ⟨equalValues, equalHeap⟩
  subst values
  subst middle
  exact diag_prime_count.result layer heap

private theorem total_call (layer : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number layer)) :
    EvaluatesRel source cacheSpec env (.call (.name "diag_total") [.name "k"]) heap
      (fun value after => value = number (SpiralPrimes.total layer) ∧ after = heap) := by
  apply EvaluatesRel.call (ArgumentsRel.fixed (.cons (Evaluates.lookup getLayer) .nil))
  rintro values middle ⟨equalValues, equalHeap⟩
  subst values
  subst middle
  apply (diag_total.memo_result layer heap cacheSpec).consequence
  rintro value after ⟨equalValue, equalHeap⟩
  refine ⟨?_, equalHeap⟩
  simpa [SpiralPrimes.total] using equalValue

private theorem left_product (layer den : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number layer)) (getDen : env "den" = some (number den)) :
    EvaluatesRel source cacheSpec env
      (.binOp (.name "den") .mult (.call (.name "diag_prime_count") [.name "k"])) heap
      (fun value after => value = number ((den : Int) * SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra) := by
  apply EvaluatesRel.binary
    (rightPost := fun _ _ value after => value = number (SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra)
    (Evaluates.lookup getDen).rel
  · rintro value middle ⟨equalValue, equalHeap⟩
    subst value
    subst middle
    exact count_call layer env heap getLayer
  · rintro left middle right after ⟨equalLeft, equalHeap⟩ ⟨equalRight, extra, equalAfter⟩
    subst left
    subst middle
    subst right
    subst after
    exact ⟨number ((den : Int) * SpiralPrimes.count layer), heap ++ extra,
      rfl, Cache.Preserves.refl, rfl, extra, rfl⟩

private theorem right_product (layer num : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number layer)) (getNum : env "num" = some (number num)) :
    EvaluatesRel source cacheSpec env
      (.binOp (.name "num") .mult (.call (.name "diag_total") [.name "k"])) heap
      (fun value after => value = number ((num : Int) * SpiralPrimes.total layer) ∧ after = heap) := by
  apply EvaluatesRel.binary
    (rightPost := fun _ _ value after => value = number (SpiralPrimes.total layer) ∧ after = heap)
    (Evaluates.lookup getNum).rel
  · rintro value middle ⟨equalValue, equalHeap⟩
    subst value
    subst middle
    exact total_call layer env heap getLayer
  · rintro left middle right after ⟨equalLeft, equalHeap⟩ ⟨equalRight, equalAfter⟩
    subst left
    subst middle
    subst right
    subst after
    exact ⟨number ((num : Int) * SpiralPrimes.total layer), heap,
      rfl, Cache.Preserves.refl, rfl, rfl⟩

/-- The source compares both exact counts in left-to-right order with a shared cache. -/
theorem result (layer num den : Nat) (heap : Mutable.Heap) :
    ReturnsRel source cacheSpec "ratio_below" [number layer, number num, number den] heap
      (fun value after => value = flag (decide (SpiralPrimes.below num den layer)) ∧ ∃ extra, after = heap ++ extra) := by
  apply BlockReturnsRel.function (by decide) rfl rfl
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.compare
    (leftPost := fun value after => value = number ((den : Int) * SpiralPrimes.count layer) ∧ ∃ extra, after = heap ++ extra)
    (rightPost := fun _ middle value after => value = number ((num : Int) * SpiralPrimes.total layer) ∧ after = middle)
  · apply left_product layer den
    · rfl
    · rfl
  · rintro left middle ⟨equalLeft, extra, equalHeap⟩
    subst left
    subst middle
    apply right_product layer num
    · rfl
    · rfl
  · rintro left middle right after ⟨equalLeft, extra, equalHeap⟩ ⟨equalRight, equalAfter⟩
    subst left
    subst middle
    subst right
    subst after
    refine ⟨flag (decide (SpiralPrimes.below num den layer)), heap ++ extra, ?_,
      Cache.Preserves.refl, rfl, extra, rfl⟩
    simp only [HeapCalls.compare, flag, ← Nat.cast_mul, SpiralPrimes.below]
    simp [HeapCalls.compareScalars, scalarCompare, evalCmpOp]
    exact Int.ofNat_lt

/-- A caller's layer and ratio remain ordinary integer source arguments. -/
theorem evaluates (layer num den : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number layer))
    (getNum : env "num" = some (number num)) (getDen : env "den" = some (number den)) :
    EvaluatesRel source cacheSpec env
      (.call (.name "ratio_below") [.name "k", .name "num", .name "den"]) heap
      (fun value after => value = flag (decide (SpiralPrimes.below num den layer)) ∧ ∃ extra, after = heap ++ extra) := by
  apply EvaluatesRel.call (ArgumentsRel.fixed
    (.cons (Evaluates.lookup getLayer) (.cons (Evaluates.lookup getNum) (.cons (Evaluates.lookup getDen) .nil))))
  rintro values middle ⟨equalValues, equalHeap⟩
  subst values
  subst middle
  exact result layer num den heap

end ratio_below

namespace naive
private abbrev source := P58Ast.module
private abbrev cacheSpec := diag_prime_count.spec
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private abbrev condition : Expr :=
  .call (.name "ratio_below") [.name "k", .name "num", .name "den"]
private abbrev sideExpression : Expr :=
  .binOp (.binOp (.constant (.int 2)) .mult (.name "k")) .add (.constant (.int 1))
private abbrev body : List Stmt :=
  [.ifThen condition [.return sideExpression] [], .augAssign (.name "k") .add (.constant (.int 1))]
private abbrev tail : List Stmt := [.whileDo (.constant (.bool true)) body []]

private theorem side_evaluates (layer : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number layer)) :
    Evaluates source cacheSpec env sideExpression heap (number (SpiralPrimes.side layer)) heap := by
  have evaluated : Evaluates source cacheSpec env sideExpression heap (number (2 * (layer : Int) + 1)) heap :=
    Evaluates.binary
      (Evaluates.binary (Evaluates.constant (value := .int 2)) (Evaluates.lookup getLayer) rfl)
      (Evaluates.constant (value := .int 1)) rfl
  simpa [SpiralPrimes.side] using evaluated

/-- A genuine finite first-crossing certificate gives a source execution of the
unbounded loop, preserving all caller objects and the cache invariant. -/
private theorem scan (num den bound fuel start : Nat)
    (first : SpiralPrimes.FirstCrossing num den bound)
    (positive : 0 < start) (inside : start ≤ bound) (window : start + fuel = bound + 1)
    (env : Mutable.Env) (heap : Mutable.Heap)
    (getLayer : env "k" = some (number start))
    (getNum : env "num" = some (number num)) (getDen : env "den" = some (number den)) :
    BlockReturnsRel source cacheSpec env tail heap
      (fun value after => value = number (SpiralPrimes.side bound) ∧ ∃ extra, after = heap ++ extra) := by
  induction fuel generalizing start env heap with
  | zero => omega
  | succ fuel ih =>
      apply BlockReturnsRel.while_loop
      · exact (Evaluates.constant (value := .bool true)).rel
      · rintro tested middle ⟨equalValue, equalHeap⟩
        subst tested
        subst middle
        refine ⟨true, rfl, ?_⟩
        apply BlockReturnsRel.branch (ratio_below.evaluates start num den env heap getLayer getNum getDen)
        rintro tested middle ⟨equalValue, extra, equalHeap⟩
        subst tested
        subst middle
        by_cases last : start = bound
        · subst start
          refine ⟨true, ?_, ?_⟩
          · simp [Mutable.truth, scalarTruth, first.crossing]
          · apply BlockReturnsRel.return_value
            apply (side_evaluates bound env (heap ++ extra) getLayer).rel.consequence
            rintro value after ⟨equalValue, equalHeap⟩
            exact ⟨equalValue, extra, equalHeap⟩
        · have earlier : start < bound := by omega
          have notCrossed := first.earlier start positive earlier
          refine ⟨false, ?_, ?_⟩
          · simp [Mutable.truth, scalarTruth, notCrossed]
          · apply BlockReturnsRel.augAssign getLayer (Evaluates.constant (value := .int 1)).rel
            rintro right after ⟨equalRight, equalAfter⟩
            subst right
            subst after
            refine ⟨number (start + 1), heap ++ extra, rfl, Cache.Preserves.refl, ?_⟩
            apply BlockReturnsRel.consequence (pre := fun value after =>
              value = number (SpiralPrimes.side bound) ∧ ∃ more, after = (heap ++ extra) ++ more)
            · have resumed := ih (start := start + 1)
                (positive := by omega) (inside := by omega) (window := by omega)
                (env := HeapCalls.setLocal env "k" (number (start + 1))) (heap := heap ++ extra)
                (getLayer := by simp [HeapCalls.setLocal])
                (getNum := by simpa [HeapCalls.setLocal] using getNum)
                (getDen := by simpa [HeapCalls.setLocal] using getDen)
              simpa [tail, body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using resumed
            · rintro value after ⟨equalValue, more, equalHeap⟩
              exact ⟨equalValue, extra ++ more, by simpa only [List.append_assoc] using equalHeap⟩

/-- Source termination is claimed only with the explicit mathematical crossing. -/
theorem result (num den bound : Nat) (first : SpiralPrimes.FirstCrossing num den bound)
    (heap : Mutable.Heap) :
    ReturnsRel source cacheSpec "naive" [number num, number den] heap
      (fun value after => value = number (SpiralPrimes.side bound) ∧ ∃ extra, after = heap ++ extra) := by
  apply BlockReturnsRel.function (by decide) rfl rfl
  apply BlockReturnsRel.assign (Evaluates.constant (value := .int 1)).rel
  rintro value middle ⟨equalValue, equalHeap⟩
  subst value
  subst middle
  apply scan num den bound bound 1 first
  · decide
  · exact first.positive
  · omega
  · rfl
  · rfl
  · rfl

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p58

namespace data.«project-euler-statements».data.py.project_euler_statements.p58.naive_default
open FormalSW.PyAst FormalSW.PyAst.HeapMemoCalls
open ProjectEulerSolutions
private abbrev source := P58Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

/-- The zero-argument source wrapper preserves the actual cached reference scan. -/
theorem result (bound : Nat) (first : SpiralPrimes.FirstCrossing 1 10 bound) (heap : Mutable.Heap) :
    ReturnsRel source diag_prime_count.spec "naive_default" [] heap
      (fun value after => value = number (SpiralPrimes.side bound) ∧ ∃ extra, after = heap ++ extra) := by
  apply BlockReturnsRel.function (by decide) rfl rfl
  apply BlockReturnsRel.return_value
  apply EvaluatesRel.call (ArgumentsRel.fixed (.cons
    (Evaluates.constant (value := .int 1)) (.cons (Evaluates.constant (value := .int 10)) .nil)))
  rintro values middle ⟨equalValues, equalHeap⟩
  subst values
  subst middle
  exact naive.result 1 10 bound first heap

theorem returns_of_firstCrossing {bound : Nat} (first : SpiralPrimes.FirstCrossing 1 10 bound) :
    (HeapMemoCalls.scalarFunction source "naive_default" []).Returns :=
  ReturnsRel.scalar_returns ((result bound first []).consequence
    (by intro value after ⟨equal, extra, same⟩; exact ⟨equal, True.intro⟩))

end data.«project-euler-statements».data.py.project_euler_statements.p58.naive_default

namespace data.«project-euler-statements».data.py.project_euler_statements.p58
open FormalSW.PyAst

theorem diag_prime_count.«Returns» (k : Int)
    (condition : Calls.Condition P58Ast.module
      (fun key => if key = "k" then some (.int k) else none) P58Ast.requires_diag_prime_count_0) :
    (HeapMemoCalls.scalarFunction P58Ast.module "diag_prime_count" [.int k]).Returns := by
  have nonnegative : 0 ≤ k := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  have returned :
      (HeapMemoCalls.scalarFunction P58Ast.module "diag_prime_count" [.int (k.toNat : Int)]).Returns :=
    HeapMemoCalls.ReturnsRel.scalar_returns ((diag_prime_count.result k.toNat []).consequence
      (by intro value after holds; exact ⟨holds.1, True.intro⟩))
  simpa only [Int.toNat_of_nonneg nonnegative] using returned

theorem diag_prime_count.«Supported» (k : Int)
    (condition : Calls.Condition P58Ast.module
      (fun key => if key = "k" then some (.int k) else none) P58Ast.requires_diag_prime_count_0) :
    (HeapMemoCalls.scalarFunction P58Ast.module "diag_prime_count" [.int k]).Supported :=
  (diag_prime_count.«Returns» k condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p58

namespace data.«project-euler-statements».data.py.project_euler_statements.p58
open FormalSW.PyAst

/-- The original cached reference reaches the checked first crossing. -/
theorem naive_default.final_result (heap : Mutable.Heap) :
    HeapMemoCalls.ReturnsRel P58Ast.module diag_prime_count.spec "naive_default" [] heap
      (fun value after => value = .scalar (.int 26241) ∧ ∃ extra, after = heap ++ extra) := by
  simpa only [ProjectEulerSolutions.SpiralPrimes.side] using
    naive_default.result 13120 ProjectEulerSolutions.P58Numerical.first_crossing heap

theorem naive_default.«Returns» :
    (HeapMemoCalls.scalarFunction P58Ast.module "naive_default" []).Returns :=
  naive_default.returns_of_firstCrossing ProjectEulerSolutions.P58Numerical.first_crossing

theorem naive_default.«Supported» :
    (HeapMemoCalls.scalarFunction P58Ast.module "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p58
