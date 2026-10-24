import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p17.py.ast»
import FormalSW
import ProjectEulerStatements.Lib.NumberWords

namespace data.«project-euler-statements».data.py.project_euler_statements.p17
open FormalSW.PyAst
private abbrev program := P17Ast.module
variable {globals : Mutable.Globals}

private theorem argument_n (body : List Stmt) (n : Int) (globals : Mutable.Globals) :
    HeapCalls.functionEnv [{ name := "n", annotation := some (.name "int") }] body
      [.scalar (.int n)] globals "n" = some (.scalar (.int n)) := by
  cases globals <;> rfl

private def contents (entries : List (Constant × Constant)) : List (Constant × Mutable.Value) :=
  entries.foldl (fun table (key, value) => ScalarDict.insert table key (.scalar value)) []

private def small_word_len.table : List (Constant × Constant) :=
  [(.int 0, .int 0), (.int 1, .int 3), (.int 2, .int 3), (.int 3, .int 5), (.int 4, .int 4), (.int 5, .int 4), (.int 6, .int 3), (.int 7, .int 5), (.int 8, .int 5), (.int 9, .int 4), (.int 10, .int 3), (.int 11, .int 6), (.int 12, .int 6), (.int 13, .int 8), (.int 14, .int 8), (.int 15, .int 7), (.int 16, .int 7), (.int 17, .int 9), (.int 18, .int 8), (.int 19, .int 8)]

private theorem small_word_len.lookup (n : Int) :
    (ScalarDict.lookup (contents small_word_len.table) (.int n)).getD (.scalar (.int 0)) =
      .scalar (.int (ProjectEulerStatements.P17.smallWordLen n.toNat)) := by
  change (ScalarDict.lookup (α := Mutable.Value) [(.int 0, .scalar (.int 0)), (.int 1, .scalar (.int 3)), (.int 2, .scalar (.int 3)), (.int 3, .scalar (.int 5)), (.int 4, .scalar (.int 4)), (.int 5, .scalar (.int 4)), (.int 6, .scalar (.int 3)), (.int 7, .scalar (.int 5)), (.int 8, .scalar (.int 5)), (.int 9, .scalar (.int 4)), (.int 10, .scalar (.int 3)), (.int 11, .scalar (.int 6)), (.int 12, .scalar (.int 6)), (.int 13, .scalar (.int 8)), (.int 14, .scalar (.int 8)), (.int 15, .scalar (.int 7)), (.int 16, .scalar (.int 7)), (.int 17, .scalar (.int 9)), (.int 18, .scalar (.int 8)), (.int 19, .scalar (.int 8))] (.int n)).getD (.scalar (.int 0)) = _
  by_cases h0 : n = 0
  · subst n; decide
  by_cases h1 : n = 1
  · subst n; decide
  by_cases h2 : n = 2
  · subst n; decide
  by_cases h3 : n = 3
  · subst n; decide
  by_cases h4 : n = 4
  · subst n; decide
  by_cases h5 : n = 5
  · subst n; decide
  by_cases h6 : n = 6
  · subst n; decide
  by_cases h7 : n = 7
  · subst n; decide
  by_cases h8 : n = 8
  · subst n; decide
  by_cases h9 : n = 9
  · subst n; decide
  by_cases h10 : n = 10
  · subst n; decide
  by_cases h11 : n = 11
  · subst n; decide
  by_cases h12 : n = 12
  · subst n; decide
  by_cases h13 : n = 13
  · subst n; decide
  by_cases h14 : n = 14
  · subst n; decide
  by_cases h15 : n = 15
  · subst n; decide
  by_cases h16 : n = 16
  · subst n; decide
  by_cases h17 : n = 17
  · subst n; decide
  by_cases h18 : n = 18
  · subst n; decide
  by_cases h19 : n = 19
  · subst n; decide
  have zero : ProjectEulerStatements.P17.smallWordLen n.toNat = 0 := by
    have outside : n.toNat = 0 ∨ 20 ≤ n.toNat := by omega
    rcases outside with small | large
    · simp [small, ProjectEulerStatements.P17.smallWordLen]
    · obtain ⟨m, equal⟩ := Nat.exists_eq_add_of_le large
      rw [equal, Nat.add_comm]
      rfl
  rw [zero]
  simp [ScalarDict.lookup, scalarCompare, evalCmpOp, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17, Ne.symm h18, Ne.symm h19]

theorem small_word_len.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue (globals := globals) program "small_word_len" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P17.smallWordLen n.toNat)))
      (heap ++ [.dict (contents small_word_len.table)]) := by
  have found : (heap ++ [Mutable.Object.dict (contents small_word_len.table)])[heap.length]? =
      some (.dict (contents small_word_len.table)) := by simp
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.dictionary_get (entries := contents small_word_len.table)
    (by intro name equal; cases equal)
    (HeapCalls.Evaluates.dictionary_constants small_word_len.table)
  · exact found
  · exact .cons (HeapCalls.Evaluates.lookup (argument_n _ n globals)) (.cons HeapCalls.Evaluates.constant .nil)
  · change Mutable.dictionaryGet heap.length (.scalar (.int n)) (.scalar (.int 0))
      (heap ++ [.dict (contents small_word_len.table)]) = _
    rw [Mutable.dictionaryGet_scalar _ _ (contents small_word_len.table) found, small_word_len.lookup]

theorem small_word_len.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "small_word_len" [.int n]).Returns :=
  (small_word_len.result n []).scalar_returns

theorem small_word_len.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "small_word_len" [.int n]).Supported :=
  (small_word_len.«Returns» n).supported

private def tens_word_len.table : List (Constant × Constant) :=
  [(.int 2, .int 6), (.int 3, .int 6), (.int 4, .int 5), (.int 5, .int 5), (.int 6, .int 5), (.int 7, .int 7), (.int 8, .int 6), (.int 9, .int 6)]

private theorem tens_word_len.lookup (n : Int) :
    (ScalarDict.lookup (contents tens_word_len.table) (.int n)).getD (.scalar (.int 0)) =
      .scalar (.int (ProjectEulerStatements.P17.tensWordLen n.toNat)) := by
  change (ScalarDict.lookup (α := Mutable.Value) [(.int 2, .scalar (.int 6)), (.int 3, .scalar (.int 6)), (.int 4, .scalar (.int 5)), (.int 5, .scalar (.int 5)), (.int 6, .scalar (.int 5)), (.int 7, .scalar (.int 7)), (.int 8, .scalar (.int 6)), (.int 9, .scalar (.int 6))] (.int n)).getD (.scalar (.int 0)) = _
  by_cases h2 : n = 2
  · subst n; decide
  by_cases h3 : n = 3
  · subst n; decide
  by_cases h4 : n = 4
  · subst n; decide
  by_cases h5 : n = 5
  · subst n; decide
  by_cases h6 : n = 6
  · subst n; decide
  by_cases h7 : n = 7
  · subst n; decide
  by_cases h8 : n = 8
  · subst n; decide
  by_cases h9 : n = 9
  · subst n; decide
  have zero : ProjectEulerStatements.P17.tensWordLen n.toNat = 0 := by
    have outside : n.toNat < 2 ∨ 10 ≤ n.toNat := by omega
    rcases outside with small | large
    · interval_cases h : n.toNat <;> rfl
    · obtain ⟨m, equal⟩ := Nat.exists_eq_add_of_le large
      rw [equal, Nat.add_comm]
      rfl
  rw [zero]
  simp [ScalarDict.lookup, scalarCompare, evalCmpOp, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9]

theorem tens_word_len.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue (globals := globals) program "tens_word_len" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P17.tensWordLen n.toNat)))
      (heap ++ [.dict (contents tens_word_len.table)]) := by
  have found : (heap ++ [Mutable.Object.dict (contents tens_word_len.table)])[heap.length]? =
      some (.dict (contents tens_word_len.table)) := by simp
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.dictionary_get (entries := contents tens_word_len.table)
    (by intro name equal; cases equal)
    (HeapCalls.Evaluates.dictionary_constants tens_word_len.table)
  · exact found
  · exact .cons (HeapCalls.Evaluates.lookup (argument_n _ n globals)) (.cons HeapCalls.Evaluates.constant .nil)
  · change Mutable.dictionaryGet heap.length (.scalar (.int n)) (.scalar (.int 0))
      (heap ++ [.dict (contents tens_word_len.table)]) = _
    rw [Mutable.dictionaryGet_scalar _ _ (contents tens_word_len.table) found, tens_word_len.lookup]

theorem tens_word_len.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "tens_word_len" [.int n]).Returns :=
  (tens_word_len.result n []).scalar_returns

theorem tens_word_len.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "tens_word_len" [.int n]).Supported :=
  (tens_word_len.«Returns» n).supported

private theorem word_len.small (n : Int) (bound : n < 20) (heap : Mutable.Heap) :
    ∃ extra, HeapCalls.ReturnsValue (globals := globals) program "word_len" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P17.wordLen n.toNat))) (heap ++ extra) := by
  have mathematical : ProjectEulerStatements.P17.wordLen n.toNat =
      ProjectEulerStatements.P17.smallWordLen n.toNat :=
    ProjectEulerStatements.P17.wordLen_below_twenty _ (by omega)
  rw [mathematical]
  by_cases zero : n = 0
  · subst n
    refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply HeapCalls.BlockReturns.function rfl rfl
    apply HeapCalls.BlockReturns.branch (flag := true)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool true)) (finalHeap := heap) (HeapCalls.Evaluates.lookup (argument_n _ 0 globals)) HeapCalls.Evaluates.constant rfl) rfl
    exact HeapCalls.BlockReturns.return_value HeapCalls.Evaluates.constant
  · refine ⟨[.dict (contents small_word_len.table)], ?_⟩
    apply HeapCalls.BlockReturns.function rfl rfl
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap) (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, zero])) rfl
    apply HeapCalls.BlockReturns.branch (flag := true)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool true)) (finalHeap := heap) (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, bound])) rfl
    exact HeapCalls.BlockReturns.return_value
      (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup (argument_n _ n globals)) .nil) (small_word_len.result n heap))

private theorem word_len.below_hundred (n : Nat) (bound : n < 100) (heap : Mutable.Heap) :
    ∃ extra, HeapCalls.ReturnsValue (globals := globals) program "word_len" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P17.wordLen n))) (heap ++ extra) := by
  by_cases small : n < 20
  · simpa using word_len.small n (by omega) heap
  · refine ⟨[.dict (contents tens_word_len.table), .dict (contents small_word_len.table)], ?_⟩
    rw [ProjectEulerStatements.P17.wordLen_below_hundred n bound, if_neg small]
    apply HeapCalls.BlockReturns.function rfl rfl
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap) (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, show n ≠ 0 by omega])) rfl
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap) (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, small])) rfl
    apply HeapCalls.BlockReturns.branch (flag := true)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool true)) (finalHeap := heap) (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, bound])) rfl
    apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.binary
    · apply HeapCalls.Evaluates.call (.cons
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant rfl) .nil)
      exact tens_word_len.result ((n : Int) / 10) heap
    · apply HeapCalls.Evaluates.call (.cons
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant rfl) .nil)
      exact small_word_len.result ((n : Int) % 10) _
    · simp [Mutable.binary, scalarBinary, Int.toNat_emod, List.append_assoc]
      rfl

private abbrev remainderExpression : Expr :=
  .ifExp (.compare (.name "r") [(.eq, .constant (.int 0))]) (.constant (.int 0))
    (.binOp (.constant (.int 3)) .add (.call (.name "word_len") [.name "r"]))

private theorem word_len.remainder (r : Nat) (bound : r < 100) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (getR : env "r" = some (.scalar (.int r))) :
    ∃ extra, HeapCalls.Evaluates (globals := globals) program env remainderExpression heap
      (.scalar (.int (if r = 0 then 0 else 3 + ProjectEulerStatements.P17.wordLen r))) (heap ++ extra) := by
  by_cases zero : r = 0
  · subst r
    refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply HeapCalls.Evaluates.conditional
      (HeapCalls.Evaluates.compare (value := .scalar (.bool true)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup getR) HeapCalls.Evaluates.constant rfl) rfl
    exact HeapCalls.Evaluates.constant
  · obtain ⟨extra, called⟩ := word_len.below_hundred r bound heap
    refine ⟨extra, ?_⟩
    rw [if_neg zero]
    apply HeapCalls.Evaluates.conditional
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup getR) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, zero])) rfl
    apply HeapCalls.Evaluates.binary HeapCalls.Evaluates.constant
      (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup getR) .nil) called)
    rfl

private abbrev wordTail : List Stmt :=
  (executableBody ((findFunctionIn program.body "word_len").getD ([], [])).2).drop 3

private theorem word_len.tail (n : Nat) (large : 100 ≤ n) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (getN : env "n" = some (.scalar (.int n))) :
    ∃ extra, HeapCalls.BlockReturns (globals := globals) program env wordTail heap
      (.scalar (.int (ProjectEulerStatements.P17.wordLen n))) (heap ++ extra) := by
  by_cases hundreds : n < 1000
  · let pair : Mutable.Object := .tuple [.scalar (.int ((n / 100 : Nat) : Int)), .scalar (.int ((n % 100 : Nat) : Int))]
    let unpacked := HeapCalls.assignNames env ["h", "r"]
      [.scalar (.int ((n / 100 : Nat) : Int)), .scalar (.int ((n % 100 : Nat) : Int))]
    let beforeRemainder := heap ++ [pair, .dict (contents small_word_len.table)]
    obtain ⟨extra, remainder⟩ := word_len.remainder (n % 100) (Nat.mod_lt _ (by decide))
      beforeRemainder unpacked (by simp [unpacked, HeapCalls.assignNames, HeapCalls.setLocal])
    refine ⟨[pair, .dict (contents small_word_len.table)] ++ extra, ?_⟩
    rw [ProjectEulerStatements.P17.wordLen_hundreds n large hundreds]
    apply HeapCalls.BlockReturns.branch (flag := true)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool true)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup getN) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, hundreds])) rfl
    apply HeapCalls.BlockReturns.unpack
      (items := [.scalar (.int ((n / 100 : Nat) : Int)), .scalar (.int ((n % 100 : Nat) : Int))])
      (afterUnpack := heap ++ [pair]) rfl
    · apply HeapCalls.Evaluates.builtin
        (.cons (HeapCalls.Evaluates.lookup getN) (.cons HeapCalls.Evaluates.constant .nil))
      have divided := Mutable.divmod_ints (n : Int) 100 (by decide) heap
      have quotient : (n : Int).fdiv 100 = ((n / 100 : Nat) : Int) := by
        rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
        rfl
      have remaining : (n : Int) - 100 * (n : Int).fdiv 100 = ((n % 100 : Nat) : Int) := by
        rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), ← Int.emod_def]
        rfl
      simpa only [quotient, remaining] using divided
    · simp [Mutable.sequence, pair, Int.emod_def]
    · rfl
    · apply HeapCalls.BlockReturns.return_value
      apply HeapCalls.Evaluates.binary
      · apply HeapCalls.Evaluates.binary
        · apply HeapCalls.Evaluates.call (values := [.scalar (.int ((n / 100 : Nat) : Int))])
            (.cons (HeapCalls.Evaluates.lookup
              (by simp [HeapCalls.assignNames, HeapCalls.setLocal])) .nil)
          exact small_word_len.result (n / 100 : Nat) (heap ++ [pair])
        · exact HeapCalls.Evaluates.constant
        · rfl
      · simpa only [beforeRemainder, unpacked, List.append_assoc] using remainder
      · simp [Mutable.binary, scalarBinary]
        rfl
  · refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup getN) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, hundreds])) rfl
    by_cases thousand : n = 1000
    · subst n
      rw [ProjectEulerStatements.P17.wordLen_thousand]
      apply HeapCalls.BlockReturns.branch (flag := true)
        (HeapCalls.Evaluates.compare (value := .scalar (.bool true)) (finalHeap := heap)
          (HeapCalls.Evaluates.lookup getN) HeapCalls.Evaluates.constant rfl) rfl
      exact HeapCalls.BlockReturns.return_value
        (HeapCalls.Evaluates.binary HeapCalls.Evaluates.constant HeapCalls.Evaluates.constant rfl)
    · rw [ProjectEulerStatements.P17.wordLen_above_thousand n (by omega)]
      apply HeapCalls.BlockReturns.branch (flag := false)
        (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap)
          (HeapCalls.Evaluates.lookup getN) HeapCalls.Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, show (n : Int) ≠ 1000 by omega])) rfl
      exact HeapCalls.BlockReturns.return_value HeapCalls.Evaluates.constant

theorem word_len.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, HeapCalls.ReturnsValue (globals := globals) program "word_len" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P17.wordLen n))) (heap ++ extra) := by
  by_cases small : n < 100
  · exact word_len.below_hundred n small heap
  · obtain ⟨extra, tail⟩ := word_len.tail n (by omega) heap
      (HeapCalls.functionEnv [{ name := "n", annotation := some (.name "int") }]
        ((findFunctionIn program.body "word_len").getD ([], [])).2 [.scalar (.int n)] globals)
        (by cases globals <;> rfl)
    refine ⟨extra, ?_⟩
    apply HeapCalls.BlockReturns.function rfl rfl
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, show n ≠ 0 by omega])) rfl
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, show ¬n < 20 by omega])) rfl
    apply HeapCalls.BlockReturns.branch (flag := false)
      (HeapCalls.Evaluates.compare (value := .scalar (.bool false)) (finalHeap := heap)
        (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, small])) rfl
    exact tail

theorem word_len.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "word_len" [.int n]).Returns := by
  by_cases nonnegative : 0 ≤ n
  · lift n to Nat using nonnegative
    obtain ⟨extra, returned⟩ := word_len.result n []
    exact returned.scalar_returns
  · obtain ⟨extra, returned⟩ := word_len.small n (by omega) []
    exact returned.scalar_returns

theorem word_len.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "word_len" [.int n]).Supported :=
  (word_len.«Returns» n).supported

private abbrev sumElement : Expr := .call (.name "word_len") [.name "i"]
private abbrev sumBody : List Stmt := HeapCalls.sumBody sumElement []

/-- Each finite range iteration may allocate privately; the entry heap is preserved. -/
private theorem naive.loop (count first : Nat) (initial : Int) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (accumulator : env HeapCalls.sumAccumulator = some (.scalar (.int initial))) :
    ∃ extra, HeapCalls.BlockReturns (globals := globals) program env
      [.rangeStepLoop "i" (first : Int) ((first + count : Nat) : Int) 1 sumBody [],
        .return (.name HeapCalls.sumAccumulator)] heap
      (.scalar (.int (initial + ((List.range' first count).map
        (fun i => (ProjectEulerStatements.P17.wordLen i : Int))).sum))) (heap ++ extra) := by
  induction count generalizing first initial heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [Nat.add_zero, List.range'_zero, List.map_nil, List.sum_nil, Int.add_zero, List.append_nil]
      apply HeapCalls.BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup accumulator)
  | succ count ih =>
      let withI := HeapCalls.setLocal env "i" (.scalar (.int first))
      let nextEnv := HeapCalls.setLocal withI HeapCalls.sumAccumulator
        (.scalar (.int (initial + ProjectEulerStatements.P17.wordLen first)))
      obtain ⟨allocated, called⟩ := word_len.result first heap
      obtain ⟨later, continued⟩ := ih (first + 1) (initial + ProjectEulerStatements.P17.wordLen first)
        (heap ++ allocated) nextEnv (by simp [nextEnv, HeapCalls.setLocal])
      refine ⟨allocated ++ later, ?_⟩
      apply HeapCalls.BlockReturns.range_step (by simp [Calls.rangeContinues])
      apply HeapCalls.BlockReturns.assign (value := .scalar (.int (initial + ProjectEulerStatements.P17.wordLen first)))
        (middle := heap ++ allocated)
      · apply HeapCalls.Evaluates.binary
          (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal, HeapCalls.sumAccumulator] using accumulator))
          (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal])) .nil) called)
        rfl
      · change HeapCalls.BlockReturns (globals := globals) program nextEnv
          [.rangeStepLoop "i" ((first : Int) + 1) ((first + (count + 1) : Nat) : Int) 1 sumBody [],
            .return (.name HeapCalls.sumAccumulator)] (heap ++ allocated) _ _
        simpa only [List.range'_succ, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm, List.append_assoc] using continued

theorem naive.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, HeapCalls.ReturnsValue (globals := globals) program "naive" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P17.naive n))) (heap ++ extra) := by
  let env := HeapCalls.functionEnv [{ name := "n", annotation := some (.name "int") }]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [.scalar (.int n)] globals
  let summed := HeapCalls.setLocal (HeapCalls.comprehensionEnv env
    [("i", .call (.name "range") [.binOp (.name "n") .add (.constant (.int 1))], [])])
    HeapCalls.sumAccumulator (.scalar (.int 0))
  obtain ⟨extra, loop⟩ := naive.loop (n + 1) 0 0 heap summed (by simp [summed, HeapCalls.setLocal])
  have total : ((List.range' 0 (n + 1)).map
      (fun i => (ProjectEulerStatements.P17.wordLen i : Int))).sum =
        (ProjectEulerStatements.P17.naive n : Int) := by
    rw [← List.range_eq_range']
    have natural : ((List.range (n + 1)).map ProjectEulerStatements.P17.wordLen).sum =
        ProjectEulerStatements.P17.naive n := by
      rw [List.sum_eq_foldl, List.foldl_map]
      rfl
    simpa using congrArg (fun x : Nat => (x : Int)) natural
  refine ⟨extra, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_range
  apply HeapCalls.Evaluates.sum_generator_range
    (.cons (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant rfl) .nil)
    rfl HeapCalls.Evaluates.constant rfl
  simpa only [Nat.zero_add, Int.zero_add, total] using loop

private theorem naive.negative (n : Int) (negative : n < 0) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue (globals := globals) program "naive" [.scalar (.int n)] heap (.scalar (.int 0)) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_range
  apply HeapCalls.Evaluates.sum_generator_range
    (.cons (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup (argument_n _ n globals)) HeapCalls.Evaluates.constant rfl) .nil)
    rfl HeapCalls.Evaluates.constant rfl
  apply HeapCalls.BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup (by simp [HeapCalls.setLocal]))

theorem naive.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  by_cases nonnegative : 0 ≤ n
  · lift n to Nat using nonnegative
    obtain ⟨extra, returned⟩ := naive.result n []
    exact returned.scalar_returns
  · exact (naive.negative n (by omega) []).scalar_returns

theorem naive.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Supported :=
  (naive.«Returns» n).supported

end data.«project-euler-statements».data.py.project_euler_statements.p17
