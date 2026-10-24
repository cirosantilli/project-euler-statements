import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p4.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P4

namespace data.«project-euler-statements».data.py.project_euler_statements.p4
open FormalSW.PyAst

private theorem common_extension : HeapCalls.Extends P4Ast.module CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := P4Ast.module.body.take 2 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["naive"] at member
    have only : name = "naive" := by simpa using member
    subst name
    decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

/-- Reuse the helper's source proof in the linked problem-4 module. -/
theorem digits_result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue P4Ast.module "digits_le" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [Mutable.Object.list ((Nat.digits 10 n).map (fun (digit : Nat) => .scalar (.int (digit : Int))))]) :=
  (common.digits_le.decimal n heap).extend common_extension

private def digitValues (n : Nat) : List Mutable.Value :=
  (Nat.digits 10 n).map (fun (digit : Nat) => .scalar (.int (digit : Int)))

/-- The Python equality and eager reversed copy implement the mathematical
palindrome predicate, including the empty digit list for zero. -/
theorem palindrome_test (n : Nat) (heap : Mutable.Heap) (env : Mutable.Env)
    (getDigits : env "ds" = some (.ref heap.length)) :
    HeapCalls.Evaluates P4Ast.module env
      (.compare (.name "ds") [(.eq, .reversedList (.name "ds"))])
      (heap ++ [Mutable.Object.list (digitValues n)]) (.scalar (.bool (decide (ProjectEulerStatements.P4.isPalindrome n))))
      (heap ++ [Mutable.Object.list (digitValues n)] ++ [Mutable.Object.list ((digitValues n).reverse)]) := by
  apply HeapCalls.Evaluates.compare
    (HeapCalls.Evaluates.lookup getDigits)
    (HeapCalls.Evaluates.reversed_list (items := digitValues n) (HeapCalls.Evaluates.lookup getDigits) (by simp))
  have result := HeapCalls.compare_int_lists
    ((Nat.digits 10 n).map (fun (d : Nat) => (d : Int)))
    (((Nat.digits 10 n).reverse).map (fun (d : Nat) => (d : Int)))
    (heap := heap ++ [Mutable.Object.list (digitValues n)] ++ [Mutable.Object.list ((digitValues n).reverse)])
    (a := heap.length) (b := (heap ++ [Mutable.Object.list (digitValues n)]).length)
    (by simp [digitValues, List.map_map])
    (by simp [digitValues, List.map_map, List.map_reverse])
  have injective : Function.Injective (List.map (fun d : Nat => (d : Int))) :=
    List.map_injective_iff.mpr Nat.cast_injective
  simpa only [ProjectEulerStatements.P4.isPalindrome, injective.eq_iff] using result

private def innerBody : List Stmt :=
  match executableBody ((findFunctionIn P4Ast.module.body "naive").getD ([], [])).2 with
  | [_, _, _, .forIn _ _ [.forIn _ _ body _] _, _] => body
  | _ => []

/-- One actual inner-loop iteration computes its product, converts the digits,
tests the palindrome, and updates the running maximum. -/
theorem product_step (a b best : Nat) (heap : Mutable.Heap) (env : Mutable.Env)
    (getA : env "a" = some (.scalar (.int a)))
    (getB : env "b" = some (.scalar (.int b)))
    (getBest : env "max_" = some (.scalar (.int best))) :
    HeapCalls.BlockReturns P4Ast.module env (innerBody ++ [.return (.name "max_")]) heap
      (.scalar (.int (if ProjectEulerStatements.P4.isPalindrome (a * b) then max (a * b) best else best)))
      (heap ++ [Mutable.Object.list (digitValues (a * b))] ++ [Mutable.Object.list ((digitValues (a * b)).reverse)]) := by
  apply HeapCalls.BlockReturns.assign
    (value := .scalar (.int ((a * b : Nat) : Int))) (middle := heap)
  · exact HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getA) (HeapCalls.Evaluates.lookup getB)
      (by simp [Mutable.binary, scalarBinary])
  · apply HeapCalls.BlockReturns.assign
      (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal])) .nil)
        (digits_result (a * b) heap))
    by_cases palindrome : ProjectEulerStatements.P4.isPalindrome (a * b)
    · simp only [palindrome, if_true]
      apply HeapCalls.BlockReturns.branch (flag := true)
      · simpa only [palindrome, decide_true] using
          palindrome_test (a * b) heap _ (by simp [HeapCalls.setLocal])
      · simp [Mutable.truth, scalarTruth]
      · apply HeapCalls.BlockReturns.assign
          (value := .scalar (.int ((max (a * b) best : Nat) : Int)))
          (middle := heap ++ [Mutable.Object.list (digitValues (a * b))] ++ [Mutable.Object.list ((digitValues (a * b)).reverse)])
        · apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup
            (value := .scalar (.int ((a * b : Nat) : Int))) (by simp [HeapCalls.setLocal]))
            (.cons (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using getBest)) .nil))
          simp [HeapCalls.primitive, Calls.positionalMaximum, Calls.maximumFrom, HeapCalls.scalarResult,
            scalarCompare, evalCmpOp]
          split <;> simp_all [max_def]
          omega
        · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal]))
    · simp only [palindrome, if_false]
      apply HeapCalls.BlockReturns.branch (flag := false)
      · simpa only [palindrome, decide_false] using
          palindrome_test (a * b) heap _ (by simp [HeapCalls.setLocal])
      · simp [Mutable.truth, scalarTruth]
      · exact HeapCalls.BlockReturns.return_value
          (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using getBest))

private def productBest (a b best : Nat) : Nat :=
  if ProjectEulerStatements.P4.isPalindrome (a * b) then max (a * b) best else best

private def productEnv (env : Mutable.Env) (a b best : Nat) (heap : Mutable.Heap) : Mutable.Env :=
  let assigned := HeapCalls.setLocal
    (HeapCalls.setLocal env "prod" (.scalar (.int ((a * b : Nat) : Int)))) "ds" (.ref heap.length)
  if ProjectEulerStatements.P4.isPalindrome (a * b) then
    HeapCalls.setLocal assigned "max_" (.scalar (.int ((max (a * b) best : Nat) : Int)))
  else assigned

private def productHeap (a b : Nat) (heap : Mutable.Heap) : Mutable.Heap :=
  heap ++ [Mutable.Object.list (digitValues (a * b))] ++ [Mutable.Object.list ((digitValues (a * b)).reverse)]

private theorem productEnv_frame (name : String) (env : Mutable.Env) (a b best : Nat)
    (heap : Mutable.Heap) (hp : name ≠ "prod") (hd : name ≠ "ds") (hm : name ≠ "max_") :
    productEnv env a b best heap name = env name := by
  simp only [productEnv]
  split <;> simp [HeapCalls.setLocal, hp, hd, hm]

private theorem productEnv_best (env : Mutable.Env) (a b best : Nat) (heap : Mutable.Heap)
    (getBest : env "max_" = some (.scalar (.int best))) :
    productEnv env a b best heap "max_" = some (.scalar (.int (productBest a b best))) := by
  simp only [productEnv, productBest]
  split <;> simp_all [HeapCalls.setLocal]

/-- The same iteration can be composed with either loop's continuation. -/
theorem product_continues (a b best : Nat) (heap : Mutable.Heap) (env : Mutable.Env)
    (getA : env "a" = some (.scalar (.int a)))
    (getB : env "b" = some (.scalar (.int b)))
    (getBest : env "max_" = some (.scalar (.int best))) :
    HeapCalls.BlockContinues P4Ast.module env innerBody heap
      (productEnv env a b best heap) (productHeap a b heap) := by
  apply HeapCalls.BlockContinues.append (body := [innerBody[0]'(by decide)])
    (HeapCalls.BlockContinues.assign (value := .scalar (.int ((a * b : Nat) : Int)))
      (finalHeap := heap) (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getA)
        (HeapCalls.Evaluates.lookup getB) (by simp [Mutable.binary, scalarBinary])))
  apply HeapCalls.BlockContinues.append (body := [innerBody[1]'(by decide)])
    (HeapCalls.BlockContinues.assign
      (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal])) .nil)
        (digits_result (a * b) heap)))
  by_cases palindrome : ProjectEulerStatements.P4.isPalindrome (a * b)
  · apply HeapCalls.BlockContinues.branch (flag := true)
    · simpa only [palindrome, decide_true] using
        palindrome_test (a * b) heap _ (by simp [HeapCalls.setLocal])
    · simp [Mutable.truth, scalarTruth]
    · simp only [productEnv, palindrome, ite_true]
      apply HeapCalls.BlockContinues.assign
      apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup
        (value := .scalar (.int ((a * b : Nat) : Int))) (by simp [HeapCalls.setLocal]))
        (.cons (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using getBest)) .nil))
      simp [HeapCalls.primitive, Calls.positionalMaximum, Calls.maximumFrom, HeapCalls.scalarResult,
        scalarCompare, evalCmpOp, productHeap]
      split <;> simp_all [max_def]
      omega
  · apply HeapCalls.BlockContinues.branch (flag := false)
    · simpa only [palindrome, decide_false] using
        palindrome_test (a * b) heap _ (by simp [HeapCalls.setLocal])
    · simp [Mutable.truth, scalarTruth]
    · simpa only [ite_false, productEnv, palindrome, if_false, productHeap] using
        (HeapCalls.BlockContinues.nil (module := P4Ast.module))

private def rowBest (a start : Nat) : Nat → Nat → Nat
  | 0, best => best
  | remaining + 1, best => rowBest a (start + 1) remaining (productBest a start best)

/-- The inner range visits every factor in ascending order, preserving the
upper bound while accumulating the maximum of the tested palindromes. -/
theorem inner_loop (remaining start stop a best : Nat) (bound : stop = start + remaining)
    (heap : Mutable.Heap) (env : Mutable.Env)
    (getA : env "a" = some (.scalar (.int a)))
    (getBest : env "max_" = some (.scalar (.int best))) :
    ∃ finalEnv finalHeap,
      HeapCalls.BlockContinues P4Ast.module env
        [.rangeStepLoop "b" start stop 1 innerBody []] heap finalEnv finalHeap ∧
      finalEnv "hi" = env "hi" ∧
      finalEnv "max_" = some (.scalar (.int (rowBest a start remaining best))) := by
  induction remaining generalizing start best heap env with
  | zero =>
      exact ⟨env, heap, HeapCalls.BlockContinues.range_done
        (by simp [Calls.rangeContinues, bound]) HeapCalls.BlockContinues.nil, rfl, getBest⟩
  | succ remaining ih =>
      let stepEnv := HeapCalls.setLocal env "b" (.scalar (.int start))
      have run := product_continues a start best heap stepEnv
        (by simpa [stepEnv, HeapCalls.setLocal] using getA)
        (by simp [stepEnv, HeapCalls.setLocal])
        (by simpa [stepEnv, HeapCalls.setLocal] using getBest)
      obtain ⟨finalEnv, finalHeap, tail, preserveHi, result⟩ :=
        ih (start + 1) (productBest a start best) (by omega) (productHeap a start heap)
          (productEnv stepEnv a start best heap)
          (by rw [productEnv_frame "a" _ _ _ _ _ (by decide) (by decide) (by decide)]
              simpa [stepEnv, HeapCalls.setLocal] using getA)
          (productEnv_best _ _ _ _ _ (by simpa [stepEnv, HeapCalls.setLocal] using getBest))
      refine ⟨finalEnv, finalHeap, HeapCalls.BlockContinues.range_step
        (by simp [Calls.rangeContinues]; omega) ?_, ?_, result⟩
      · apply run.append
        simpa [Calls.loopContinuation, innerBody, Int.natCast_add] using tail
      · rw [preserveHi, productEnv_frame "hi" _ _ _ _ _ (by decide) (by decide) (by decide)]
        simp [stepEnv, HeapCalls.setLocal]

private def outerBody : List Stmt :=
  match executableBody ((findFunctionIn P4Ast.module.body "naive").getD ([], [])).2 with
  | [_, _, _, .forIn _ _ body _, _] => body
  | _ => []

private def outerBest (start : Nat) : Nat → Nat → Nat → Nat
  | 0, _, best => best
  | remaining + 1, hi, best =>
      outerBest (start + 1) remaining hi (rowBest start start (hi + 1 - start) best)

/-- Both source loops terminate and compute the maximum over their triangular
search region; the allocated digit lists remain in the resulting shared heap. -/
theorem outer_loop (remaining start hi best : Nat) (bound : hi + 1 = start + remaining)
    (heap : Mutable.Heap) (env : Mutable.Env)
    (getHi : env "hi" = some (.scalar (.int hi)))
    (getBest : env "max_" = some (.scalar (.int best))) :
    ∃ finalEnv finalHeap,
      HeapCalls.BlockContinues P4Ast.module env
        [.rangeStepLoop "a" start (hi + 1) 1 outerBody []] heap finalEnv finalHeap ∧
      finalEnv "hi" = env "hi" ∧
      finalEnv "max_" = some (.scalar (.int (outerBest start remaining hi best))) := by
  induction remaining generalizing start best heap env with
  | zero =>
      exact ⟨env, heap, HeapCalls.BlockContinues.range_done
        (by simp [Calls.rangeContinues]; omega) HeapCalls.BlockContinues.nil, rfl, getBest⟩
  | succ remaining ih =>
      let stepEnv := HeapCalls.setLocal env "a" (.scalar (.int start))
      obtain ⟨rowEnv, rowHeap, rowRun, rowHi, rowResult⟩ :=
        inner_loop (hi + 1 - start) start (hi + 1) start best (by omega) heap stepEnv
          (by simp [stepEnv, HeapCalls.setLocal])
          (by simpa [stepEnv, HeapCalls.setLocal] using getBest)
      have row : HeapCalls.BlockContinues P4Ast.module stepEnv outerBody heap rowEnv rowHeap := by
        apply HeapCalls.BlockContinues.for_range (middle := heap)
          (values := [.scalar (.int start), .scalar (.int ((hi + 1 : Nat) : Int))])
        · exact .cons (HeapCalls.Evaluates.lookup (by simp [stepEnv, HeapCalls.setLocal]))
            (.cons (HeapCalls.Evaluates.binary
              (HeapCalls.Evaluates.lookup (by simpa [stepEnv, HeapCalls.setLocal] using getHi))
              HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil)
        · rfl
        · exact rowRun
      obtain ⟨finalEnv, finalHeap, tail, preserveHi, result⟩ :=
        ih (start + 1) (rowBest start start (hi + 1 - start) best) (by omega) rowHeap rowEnv
          (by rw [rowHi]; simpa [stepEnv, HeapCalls.setLocal] using getHi) rowResult
      refine ⟨finalEnv, finalHeap, HeapCalls.BlockContinues.range_step
        (by simp [Calls.rangeContinues]; omega) ?_, ?_, result⟩
      · apply row.append
        simpa [Calls.loopContinuation, outerBody, Int.natCast_add] using tail
      · rw [preserveHi, rowHi]
        simp [stepEnv, HeapCalls.setLocal]

private theorem lower_evaluates (n : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getN : env "n" = some (.scalar (.int n))) :
    HeapCalls.Evaluates P4Ast.module env
      (.ifExp (.compare (.name "n") [(.eq, .constant (.int 0))]) (.constant (.int 0))
        (.binOp (.constant (.int 10)) .pow (.binOp (.name "n") .sub (.constant (.int 1)))))
      heap (.scalar (.int (ProjectEulerStatements.P4.digitLower n))) heap := by
  cases n with
  | zero =>
      apply HeapCalls.Evaluates.conditional (flag := true) (middle := heap)
      · exact HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup getN)
          HeapCalls.Evaluates.constant rfl
      · rfl
      · exact HeapCalls.Evaluates.constant
  | succ n =>
      apply HeapCalls.Evaluates.conditional (value := .scalar (.bool false)) (flag := false) (middle := heap)
      · exact HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup getN) HeapCalls.Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)
      · rfl
      · apply HeapCalls.Evaluates.binary HeapCalls.Evaluates.constant (bv := .scalar (.int n))
          (middle := heap) (afterRight := heap)
        · exact HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getN)
            HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary])
        · simp [Mutable.binary, scalarBinary, ProjectEulerStatements.P4.digitLower, show ¬ (n : Int) < 0 by omega]

private theorem upper_evaluates (n : Nat) (env : Mutable.Env) (heap : Mutable.Heap)
    (getN : env "n" = some (.scalar (.int n))) :
    HeapCalls.Evaluates P4Ast.module env
      (.binOp (.binOp (.constant (.int 10)) .pow (.name "n")) .sub (.constant (.int 1)))
      heap (.scalar (.int (ProjectEulerStatements.P4.digitUpper n))) heap := by
  apply HeapCalls.Evaluates.binary (av := .scalar (.int ((10 ^ n : Nat) : Int)))
    (bv := .scalar (.int 1)) (middle := heap) (afterRight := heap)
  · exact HeapCalls.Evaluates.binary HeapCalls.Evaluates.constant (HeapCalls.Evaluates.lookup getN)
      (by simp [Mutable.binary, scalarBinary, show ¬ (n : Int) < 0 by omega])
  · exact HeapCalls.Evaluates.constant
  · have positive : 1 ≤ (10 : Nat) ^ n := Nat.one_le_pow n 10 (by decide)
    simp [Mutable.binary, scalarBinary, ProjectEulerStatements.P4.digitUpper, Int.natCast_sub positive]

private def initialEnv (n : Nat) : Mutable.Env :=
  HeapCalls.setLocal (HeapCalls.setLocal (HeapCalls.setLocal
    (HeapCalls.argumentEnv ((findFunctionIn P4Ast.module.body "naive").getD ([], [])).1 [.scalar (.int n)])
    "lo" (.scalar (.int (ProjectEulerStatements.P4.digitLower n))))
    "hi" (.scalar (.int (ProjectEulerStatements.P4.digitUpper n)))) "max_" (.scalar (.int 0))

private theorem digit_bounds (n : Nat) :
    ProjectEulerStatements.P4.digitLower n ≤ ProjectEulerStatements.P4.digitUpper n + 1 := by
  cases n with
  | zero => decide
  | succ n =>
      have positive : 1 ≤ (10 : Nat) ^ (n + 1) := Nat.one_le_pow _ _ (by decide)
      simp only [ProjectEulerStatements.P4.digitLower, ProjectEulerStatements.P4.digitUpper]
      rw [Nat.sub_add_cancel positive, Nat.pow_succ]
      omega

private def searchResult (n : Nat) : Nat :=
  outerBest (ProjectEulerStatements.P4.digitLower n)
    (ProjectEulerStatements.P4.digitUpper n + 1 - ProjectEulerStatements.P4.digitLower n)
    (ProjectEulerStatements.P4.digitUpper n) 0

/-- Execute the actual Python function, including zero-digit input and all
intermediate allocations, for any initial shared heap. -/
theorem naive.result (n : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue P4Ast.module "naive" [.scalar (.int n)] heap
      (.scalar (.int (searchResult n))) finalHeap := by
  obtain ⟨finalEnv, finalHeap, loops, _, result⟩ := outer_loop
    (ProjectEulerStatements.P4.digitUpper n + 1 - ProjectEulerStatements.P4.digitLower n)
    (ProjectEulerStatements.P4.digitLower n) (ProjectEulerStatements.P4.digitUpper n) 0
    (by have := digit_bounds n; omega) heap (initialEnv n)
    (by simp [initialEnv, HeapCalls.setLocal]) (by simp [initialEnv, HeapCalls.setLocal])
  refine ⟨finalHeap, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign (lower_evaluates n _ heap rfl)
  apply HeapCalls.BlockReturns.assign (upper_evaluates n _ heap (by simp [HeapCalls.setLocal, HeapCalls.argumentEnv]))
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.for_range
    (values := [.scalar (.int (ProjectEulerStatements.P4.digitLower n)),
      .scalar (.int ((ProjectEulerStatements.P4.digitUpper n + 1 : Nat) : Int))]) (middle := heap)
  · exact .cons (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal]))
      (.cons (HeapCalls.Evaluates.binary
        (HeapCalls.Evaluates.lookup (value := .scalar (.int (ProjectEulerStatements.P4.digitUpper n)))
          (by simp [HeapCalls.setLocal]))
        HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil)
  · rfl
  · exact loops.returns (HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup result))

private theorem rowBest_le_iff (a start remaining best ceiling : Nat) :
    rowBest a start remaining best ≤ ceiling ↔ best ≤ ceiling ∧
      ∀ b, start ≤ b → b < start + remaining →
        ProjectEulerStatements.P4.isPalindrome (a * b) → a * b ≤ ceiling := by
  induction remaining generalizing start best with
  | zero =>
      simp only [rowBest, Nat.add_zero]
      constructor
      · intro h; exact ⟨h, by intros; omega⟩
      · exact And.left
  | succ remaining ih =>
      rw [rowBest, ih]
      have head : productBest a start best ≤ ceiling ↔ best ≤ ceiling ∧
          (ProjectEulerStatements.P4.isPalindrome (a * start) → a * start ≤ ceiling) := by
        by_cases palindrome : ProjectEulerStatements.P4.isPalindrome (a * start)
        · simp [productBest, palindrome, and_comm]
        · simp [productBest, palindrome]
      rw [head]
      constructor
      · rintro ⟨⟨bestBound, first⟩, rest⟩
        refine ⟨bestBound, ?_⟩
        intro b lower upper palindrome
        by_cases equal : b = start
        · subst b; exact first palindrome
        · exact rest b (by omega) (by omega) palindrome
      · rintro ⟨bestBound, all⟩
        exact ⟨⟨bestBound, all start (by omega) (by omega)⟩,
          fun b lower upper => all b (by omega) (by omega)⟩

private theorem outerBest_le_iff (remaining start hi best ceiling : Nat)
    (bound : hi + 1 = start + remaining) :
    outerBest start remaining hi best ≤ ceiling ↔ best ≤ ceiling ∧
      ∀ a b, start ≤ a → a ≤ b → b ≤ hi →
        ProjectEulerStatements.P4.isPalindrome (a * b) → a * b ≤ ceiling := by
  induction remaining generalizing start best with
  | zero =>
      simp only [outerBest]
      constructor
      · intro h; exact ⟨h, by intros; omega⟩
      · exact And.left
  | succ remaining ih =>
      rw [outerBest, ih (start + 1) _ (by omega), rowBest_le_iff]
      constructor
      · rintro ⟨⟨bestBound, first⟩, rest⟩
        refine ⟨bestBound, ?_⟩
        intro a b lower ordered upper palindrome
        by_cases equal : a = start
        · subst a; exact first b ordered (by omega) palindrome
        · exact rest a b (by omega) ordered upper palindrome
      · rintro ⟨bestBound, all⟩
        refine ⟨⟨bestBound, ?_⟩, ?_⟩
        · intro b lower upper palindrome
          exact all start b (by omega) lower (by omega) palindrome
        · intro a b lower ordered upper palindrome
          exact all a b (by omega) ordered upper palindrome

private theorem specification_le_iff (n ceiling : Nat) :
    ProjectEulerStatements.P4.naive n ≤ ceiling ↔
      ∀ value ∈ ProjectEulerStatements.P4.palProductSet n, value ≤ ceiling := by
  unfold ProjectEulerStatements.P4.naive
  dsimp only
  split
  · exact Finset.max'_le_iff _ _
  · rename_i empty
    simp [Finset.not_nonempty_iff_eq_empty.mp empty]

/-- Symmetry of multiplication turns the triangular Python search into the
square product set used by the existing mathematical specification. -/
theorem searchResult_correct (n : Nat) : searchResult n = ProjectEulerStatements.P4.naive n := by
  have searchBound (ceiling : Nat) := outerBest_le_iff
    (ProjectEulerStatements.P4.digitUpper n + 1 - ProjectEulerStatements.P4.digitLower n)
    (ProjectEulerStatements.P4.digitLower n) (ProjectEulerStatements.P4.digitUpper n) 0 ceiling
    (by have := digit_bounds n; omega)
  apply Nat.le_antisymm
  · apply (searchBound _).mpr
    refine ⟨Nat.zero_le _, ?_⟩
    intro a b lower ordered upper palindrome
    apply (specification_le_iff n _).mp (Nat.le_refl _) (a * b)
    change a * b ∈ Finset.filter ProjectEulerStatements.P4.isPalindrome (((Finset.Icc (ProjectEulerStatements.P4.digitLower n)
      (ProjectEulerStatements.P4.digitUpper n)).product (Finset.Icc
      (ProjectEulerStatements.P4.digitLower n) (ProjectEulerStatements.P4.digitUpper n))).image
      (fun p => p.1 * p.2))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩, palindrome⟩
    change (a, b) ∈ (Finset.Icc (ProjectEulerStatements.P4.digitLower n)
      (ProjectEulerStatements.P4.digitUpper n)).product (Finset.Icc
      (ProjectEulerStatements.P4.digitLower n) (ProjectEulerStatements.P4.digitUpper n))
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨lower, by omega⟩, ⟨by omega, upper⟩⟩
  · apply (specification_le_iff n _).mpr
    intro value membership
    change value ∈ Finset.filter ProjectEulerStatements.P4.isPalindrome (((Finset.Icc (ProjectEulerStatements.P4.digitLower n)
      (ProjectEulerStatements.P4.digitUpper n)).product (Finset.Icc
      (ProjectEulerStatements.P4.digitLower n) (ProjectEulerStatements.P4.digitUpper n))).image
      (fun p => p.1 * p.2)) at membership
    obtain ⟨products, palindrome⟩ := Finset.mem_filter.mp membership
    obtain ⟨⟨a, b⟩, bounds, rfl⟩ := Finset.mem_image.mp products
    change (a, b) ∈ (Finset.Icc (ProjectEulerStatements.P4.digitLower n)
      (ProjectEulerStatements.P4.digitUpper n)).product (Finset.Icc
      (ProjectEulerStatements.P4.digitLower n) (ProjectEulerStatements.P4.digitUpper n)) at bounds
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at bounds
    obtain ⟨⟨aLower, aUpper⟩, ⟨bLower, bUpper⟩⟩ := bounds
    have covers := ((searchBound (searchResult n)).mp (Nat.le_refl _)).2
    by_cases ordered : a ≤ b
    · exact covers a b aLower ordered bUpper palindrome
    · simpa [Nat.mul_comm] using covers b a bLower (by omega) aUpper
        (by simpa [Nat.mul_comm] using palindrome)

theorem naive.correct (n : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue P4Ast.module "naive" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P4.naive n))) finalHeap := by
  simpa only [searchResult_correct] using naive.result n heap

theorem naive.«Returns» (n : Int) (hp : Calls.Condition P4Ast.module
    (fun key => if key = "n" then some (.int n) else none) P4Ast.requires_naive_0) :
    (HeapCalls.scalarFunction P4Ast.module "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare hp rfl
  obtain ⟨finalHeap, executed⟩ := naive.result n.toNat []
  simpa [Int.toNat_of_nonneg nonnegative] using (executed.scalar_returns (values := [.int (n.toNat : Int)]))

theorem naive.«Supported» (n : Int) (hp : Calls.Condition P4Ast.module
    (fun key => if key = "n" then some (.int n) else none) P4Ast.requires_naive_0) :
    (HeapCalls.scalarFunction P4Ast.module "naive" [.int n]).Supported :=
  (naive.«Returns» n hp).supported

end data.«project-euler-statements».data.py.project_euler_statements.p4
