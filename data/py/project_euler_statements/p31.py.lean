import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p31.py.ast»
import lang.py.FormalSW.TruthCalls
import ProjectEulerStatements.P31
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

namespace data.«project-euler-statements».data.py.project_euler_statements.p31
open FormalSW.PyAst HeapCalls
private abbrev program := P31Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number
variable {globals : Mutable.Globals}

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  have inside : address < heap.length := by
    by_contra outside
    simp [List.getElem?_eq_none (by omega : heap.length ≤ address)] at found
  rw [List.getElem?_append_left inside]
  exact found

private abbrev args : List Arg :=
  [⟨"amt", some (.name "int"), none⟩,
   ⟨"cs", some (.subscript (.name "list") (.name "int")), none⟩]
private abbrev sourceBody := ((findFunctionIn program.body "count_ways_bound").getD ([], [])).2
private abbrev initial (amt address : Nat) (globals : Mutable.Globals) :=
  functionEnv args sourceBody [number amt, .ref address] globals
private theorem get_amount (amt address : Nat) : initial amt address globals "amt" = some (number amt) := by
  cases globals <;> rfl
private theorem get_coins (amt address : Nat) : initial amt address globals "cs" = some (.ref address) := by
  cases globals <;> rfl

private theorem count_zero (items : List Nat) : ProjectEulerStatements.P31.countWaysBound 0 items = 1 := by
  rw [ProjectEulerStatements.P31.countWaysBound]
private theorem count_nil (amt : Nat) : ProjectEulerStatements.P31.countWaysBound (amt + 1) [] = 0 := by
  rw [ProjectEulerStatements.P31.countWaysBound]
  omega
private theorem count_cons (amt c : Nat) (items : List Nat) (positive : 0 < c) :
    ProjectEulerStatements.P31.countWaysBound (amt + 1) (c :: items) =
      if amt + 1 < c then ProjectEulerStatements.P31.countWaysBound (amt + 1) items
      else ProjectEulerStatements.P31.countWaysBound (amt + 1 - c) (c :: items) +
        ProjectEulerStatements.P31.countWaysBound (amt + 1) items := by
  rw [ProjectEulerStatements.P31.countWaysBound]
  · simp [show c ≠ 0 by omega]
  · omega

private abbrev splitExpression : Expr := .tuple
  [.subscript (.name "cs") (.constant (.int 0)),
    .subscript (.name "cs") (.slice (some (.constant (.int 1))) none none)]
private abbrev splitHeap (heap : Mutable.Heap) (c : Nat) (rest : List Nat) : Mutable.Heap :=
  (heap ++ [.list (numbers rest)]) ++ [.tuple [number c, .ref heap.length]]
private abbrev bound (amt address : Nat) (heap : Mutable.Heap) (c : Nat) : HeapCalls.Env :=
  assignNames (initial amt address globals) ["c", "rest"] [number c, .ref heap.length]

private theorem split_result (amt c : Nat) (rest : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers (c :: rest)))) :
    Evaluates (globals := globals) program (initial amt address globals) splitExpression heap
      (.ref (heap.length + 1)) (splitHeap heap c rest) := by
  have head : Evaluates (globals := globals) program (initial amt address globals)
      (.subscript (.name "cs") (.constant (.int 0))) heap (number c) heap := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup (get_coins amt address)) Evaluates.constant
    simpa using Mutable.getItem_list heap address 0 (numbers (c :: rest)) found (by simp)
  have tail : Evaluates (globals := globals) program (initial amt address globals)
      (.subscript (.name "cs") (.slice (some (.constant (.int 1))) none none)) heap
      (.ref heap.length) (heap ++ [.list (numbers rest)]) := by
    apply Evaluates.slice (.cons (Evaluates.lookup (get_coins amt address))
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa using Mutable.getSlice_list_suffix heap address (numbers (c :: rest)) 1 found
  simpa [splitExpression, splitHeap] using
    Evaluates.tuple (.cons head (.cons tail .nil)) (by simp)

private theorem branch_result (amt c : Nat) (positive : 0 < c) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (getAmt : env "amt" = some (number amt))
    (getC : env "c" = some (number c)) :
    Evaluates (globals := globals) program env
      (.boolOp .or [.compare (.name "c") [(.eq, .constant (.int 0))],
        .compare (.name "amt") [(.lt, .name "c")]]) heap
      (.scalar (.bool (decide (amt < c)))) heap := by
  apply Evaluates.boolean_next (middle := heap) (flag := false) (value := .scalar (.bool false))
  · apply Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup getC) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, show c ≠ 0 by omega]
  · rfl
  · rfl
  · apply Evaluates.boolean_last
    · apply Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup getAmt) (Evaluates.lookup getC)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    · rfl

/-- The recursive source preserves every input object, allocating only slices and tuples. -/
theorem count_ways_bound.result (amt : Nat) (items : List Nat)
    (positive : ∀ c ∈ items, 0 < c) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ∃ extra, ReturnsValue (globals := globals) program "count_ways_bound" [number amt, .ref address] heap
      (number (ProjectEulerStatements.P31.countWaysBound amt items)) (heap ++ extra) := by
  induction measure : amt + items.length using Nat.strong_induction_on generalizing amt items heap address with
  | h size ih =>
      cases amt with
      | zero =>
          refine ⟨[], ?_⟩
          simp only [List.append_nil, count_zero]
          apply BlockReturns.function rfl rfl
          apply BlockReturns.branch (middle := heap) (flag := true) (value := .scalar (.bool true))
          · apply Evaluates.compare (Evaluates.lookup (get_amount 0 address)) Evaluates.constant
            rfl
          · rfl
          · exact BlockReturns.return_value Evaluates.constant
      | succ amt =>
          have notZero : Evaluates (globals := globals) program (initial (amt + 1) address globals)
              (.compare (.name "amt") [(.eq, .constant (.int 0))]) heap (.scalar (.bool false)) heap := by
            apply Evaluates.compare (Evaluates.lookup (get_amount (amt + 1) address)) Evaluates.constant
            simp [HeapCalls.compare, scalarCompare, evalCmpOp]
            omega
          cases items with
          | nil =>
              refine ⟨[], ?_⟩
              simp only [List.append_nil, count_nil]
              apply BlockReturns.function rfl rfl
              apply BlockReturns.branch (flag := false) notZero rfl
              apply BlockReturns.branch (middle := heap) (flag := true) (value := .scalar (.bool true))
              · apply Evaluates.unary (Evaluates.lookup (get_coins (amt + 1) address))
                simp [HeapCalls.unary, Mutable.truth, found]
              · rfl
              · exact BlockReturns.return_value Evaluates.constant
          | cons c rest =>
              have cPositive := positive c (by simp)
              have restPositive : ∀ x ∈ rest, 0 < x := fun x member => positive x (by simp [member])
              let middle := splitHeap heap c rest
              let env := bound (globals := globals) (amt + 1) address heap c
              have restFound : middle[heap.length]? = some (.list (numbers rest)) := by simp [middle]
              have originalFound : middle[address]? = some (.list (numbers (c :: rest))) :=
                found_append (found_append found _) _
              have getAmt : env "amt" = some (number (amt + 1)) := by
                simpa [env, bound, assignNames, setLocal] using get_amount (globals := globals) (amt + 1) address
              have getC : env "c" = some (number c) := by simp [env, assignNames, setLocal]
              have getRest : env "rest" = some (.ref heap.length) := by simp [env, assignNames, setLocal]
              have getCS : env "cs" = some (.ref address) := by
                simpa [env, bound, assignNames, setLocal] using get_coins (globals := globals) (amt + 1) address
              have enter : ∀ answer finalHeap,
                  BlockReturns (globals := globals) program env
                    ((executableBody sourceBody).drop 3) middle answer finalHeap →
                  ReturnsValue (globals := globals) program "count_ways_bound"
                    [number (amt + 1), .ref address] heap answer finalHeap := by
                intro answer finalHeap tail
                apply BlockReturns.function rfl rfl
                apply BlockReturns.branch (flag := false) notZero rfl
                apply BlockReturns.branch (middle := heap) (flag := false) (value := .scalar (.bool false))
                · apply Evaluates.unary (Evaluates.lookup (get_coins (amt + 1) address))
                  simp [HeapCalls.unary, Mutable.truth, found]
                · rfl
                · apply BlockReturns.unpack (expressions := [.name "c", .name "rest"]) (names := ["c", "rest"])
                    (items := [number c, .ref heap.length]) (middle := middle) (afterUnpack := middle) rfl
                    (split_result (globals := globals) (amt + 1) c rest heap address found)
                  · simp [middle, Mutable.sequence]
                  · rfl
                  · exact tail
              have tested := branch_result (globals := globals) (amt + 1) c cPositive middle env getAmt getC
              by_cases small : amt + 1 < c
              · obtain ⟨extra, returned⟩ := ih (amt + 1 + rest.length) (by simp only [List.length_cons] at measure; omega)
                  (amt + 1) rest restPositive middle heap.length restFound rfl
                refine ⟨[.list (numbers rest), .tuple [number c, .ref heap.length]] ++ extra, ?_⟩
                rw [count_cons amt c rest cPositive, if_pos small]
                apply enter
                apply BlockReturns.branch (flag := true) (by simpa [small] using tested) rfl
                simpa [middle, splitHeap, List.append_assoc] using
                  BlockReturns.return_value (Evaluates.call
                    (.cons (Evaluates.lookup getAmt) (.cons (Evaluates.lookup getRest) .nil)) returned)
              · obtain ⟨firstExtra, firstCall⟩ := ih (amt + 1 - c + (c :: rest).length)
                  (by simp only [List.length_cons] at measure ⊢; omega)
                  (amt + 1 - c) (c :: rest) positive middle address originalFound rfl
                obtain ⟨lastExtra, lastCall⟩ := ih (amt + 1 + rest.length)
                  (by simp only [List.length_cons] at measure; omega)
                  (amt + 1) rest restPositive (middle ++ firstExtra) heap.length (found_append restFound _) rfl
                refine ⟨[.list (numbers rest), .tuple [number c, .ref heap.length]] ++ firstExtra ++ lastExtra, ?_⟩
                rw [count_cons amt c rest cPositive, if_neg small]
                apply enter
                apply BlockReturns.branch (flag := false) (by simpa [small] using tested) rfl
                have left : Evaluates (globals := globals) program env
                    (.call (.name "count_ways_bound") [.binOp (.name "amt") .sub (.name "c"), .name "cs"])
                    middle (number (ProjectEulerStatements.P31.countWaysBound (amt + 1 - c) (c :: rest)))
                    (middle ++ firstExtra) := by
                  apply Evaluates.call _ firstCall
                  refine .cons (Evaluates.binary (middle := middle) (afterRight := middle)
                    (Evaluates.lookup getAmt) (Evaluates.lookup getC) ?_) (.cons (Evaluates.lookup getCS) .nil)
                  simp [Mutable.binary, scalarBinary, number, Int.natCast_sub (by omega : c ≤ amt + 1)]
                have right := Evaluates.call (.cons (Evaluates.lookup getAmt) (.cons (Evaluates.lookup getRest) .nil)) lastCall
                simpa [middle, splitHeap, List.append_assoc] using
                  BlockReturns.return_value (Evaluates.binary (finalHeap := middle ++ firstExtra ++ lastExtra) left right
                    (by simp [Mutable.binary, scalarBinary, number]))

/-- The global list remains an input object; every positive denomination is accepted. -/
theorem naive.result (amt : Nat) (items : List Nat) (positive : ∀ c ∈ items, 0 < c)
    (heap : Mutable.Heap) (address : Nat)
    (bound : globals.lookup "coins" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    ∃ extra, ReturnsValue (globals := globals) program "naive" [number amt] heap
      (number (ProjectEulerStatements.P31.countWaysBound amt items)) (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := count_ways_bound.result (globals := globals) amt items positive heap address found
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call _ returned
  refine .cons (Evaluates.lookup ?_) (.cons (Evaluates.lookup ?_) .nil)
  · cases globals <;> rfl
  · cases globals with
    | nil => simp at bound
    | cons head tail => exact bound

private abbrev amountEnv (amt : Int) : HeapCalls.Env :=
  fun name => if name = "amt" then some (.scalar (.int amt)) else none
private abbrev coinsEnv (address : Nat) : HeapCalls.Env :=
  fun name => if name = "cs" then some (.ref address) else none

private theorem amount_condition (amt : Int) (heap : Mutable.Heap) (_address : Nat) :
    Evaluates program (amountEnv amt) P31Ast.requires_count_ways_bound_0 heap
      (.scalar (.bool (decide (0 ≤ amt)))) heap := by
  exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
    (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])

private theorem coins_condition (_amt : Int) (items : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (items.map (fun n => .scalar (.int n))))) :
    Evaluates program (coinsEnv address) P31Ast.requires_count_ways_bound_1 heap
      (.scalar (.bool (decide (∀ c ∈ items, 0 < c)))) heap :=
  Evaluates.all_positive (name := "c") (sourceName := "cs") (values := items)
    (Evaluates.lookup rfl) (by simp [Mutable.sequence, found])

private theorem natural_inputs (amt : Int) (items : List Int) (nonnegative : 0 ≤ amt)
    (positive : ∀ c ∈ items, 0 < c) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (items.map (fun n => .scalar (.int n))))) :
    ∃ (amount : Nat) (coins : List Nat), amt = (amount : Int) ∧
      (∀ c ∈ coins, 0 < c) ∧ heap[address]? = some (.list (numbers coins)) := by
  refine ⟨amt.toNat, items.map Int.toNat, (Int.toNat_of_nonneg nonnegative).symm, ?_, ?_⟩
  · intro c member
    obtain ⟨integer, present, rfl⟩ := List.mem_map.mp member
    have greater := positive integer present
    omega
  · have encoded : numbers (items.map Int.toNat) = items.map (fun n => .scalar (.int n)) := by
      simp only [numbers, List.map_map]
      apply List.map_congr_left
      intro n member
      simp [number, Int.toNat_of_nonneg (by have := positive n member; omega : 0 ≤ n)]
    simpa only [encoded] using found

private theorem helper_domain (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (nonnegative : HeapCalls.Condition program (amountEnv amt) P31Ast.requires_count_ways_bound_0 heap)
    (positive : HeapCalls.Condition program (coinsEnv address) P31Ast.requires_count_ways_bound_1 heap) :
    ∃ (amount : Nat) (coins : List Nat), amt = (amount : Int) ∧
      (∀ c ∈ coins, 0 < c) ∧ heap[address]? = some (.list (numbers coins)) := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  have lower : 0 ≤ amt := by simpa using (amount_condition amt heap address).condition_iff.mp nonnegative
  have allPositive : ∀ c ∈ items, 0 < c := by
    simpa using (coins_condition amt items heap address found).condition_iff.mp positive
  exact natural_inputs amt items lower allPositive heap address found

theorem requires_count_ways_bound_0_supported (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (_valid : heap.Valid) (_typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.evaluate program (amountEnv amt) P31Ast.requires_count_ways_bound_0 heap).Supported :=
  Execution.supported_of_finishes (amount_condition amt heap address).finishes

theorem requires_count_ways_bound_1_supported (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (_nonnegative : HeapCalls.Condition program (amountEnv amt) P31Ast.requires_count_ways_bound_0 heap) :
    (HeapCalls.evaluate program (coinsEnv address) P31Ast.requires_count_ways_bound_1 heap).Supported := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Execution.supported_of_finishes (coins_condition amt items heap address found).finishes

theorem count_ways_bound.«Returns» (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (nonnegative : HeapCalls.Condition program (amountEnv amt) P31Ast.requires_count_ways_bound_0 heap)
    (positive : HeapCalls.Condition program (coinsEnv address) P31Ast.requires_count_ways_bound_1 heap) :
    (HeapCalls.call program "count_ways_bound" [.scalar (.int amt), .ref address] heap).Returns := by
  obtain ⟨amount, items, rfl, validCoins, found⟩ := helper_domain heap amt address typed nonnegative positive
  obtain ⟨extra, returned⟩ := count_ways_bound.result amount items validCoins heap address found
  exact returned.returns

theorem count_ways_bound.«Supported» (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (nonnegative : HeapCalls.Condition program (amountEnv amt) P31Ast.requires_count_ways_bound_0 heap)
    (positive : HeapCalls.Condition program (coinsEnv address) P31Ast.requires_count_ways_bound_1 heap) :
    (HeapCalls.call program "count_ways_bound" [.scalar (.int amt), .ref address] heap).Supported :=
  (count_ways_bound.«Returns» heap amt address valid typed nonnegative positive).supported

private abbrev context (address : Nat) : Mutable.Globals := [("coins", .ref address)]
private abbrev naiveEnv (amt : Int) (address : Nat) : HeapCalls.Env :=
  fun name => if name = "amt" then some (.scalar (.int amt)) else (context address).lookup name

private theorem naive_condition (amt : Int) (items : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (items.map (fun n => .scalar (.int n))))) :
    Evaluates (globals := context address) program (naiveEnv amt address) P31Ast.requires_naive_0 heap
      (.scalar (.bool (decide (0 ≤ amt ∧ ∀ c ∈ items, 0 < c)))) heap := by
  have first : Evaluates (globals := context address) program (naiveEnv amt address)
      (.compare (.name "amt") [(.gtE, .constant (.int 0))]) heap
      (.scalar (.bool (decide (0 ≤ amt)))) heap := by
    exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases nonnegative : 0 ≤ amt
  · simp only [nonnegative, true_and]
    apply Evaluates.boolean_next (flag := true) (by simpa [nonnegative] using first) rfl rfl
    apply Evaluates.boolean_last (value := .scalar (.bool (decide (∀ c ∈ items, 0 < c))))
    · exact Evaluates.all_positive (name := "c") (sourceName := "coins") (values := items)
        (Evaluates.lookup rfl) (by simp [Mutable.sequence, found])
    · rfl
  · have rejected : decide (0 ≤ amt ∧ ∀ c ∈ items, 0 < c) = false := by simp [nonnegative]
    rw [rejected]
    exact Evaluates.boolean_stop (flag := false) (by simpa [nonnegative] using first) rfl rfl

theorem requires_naive_0_supported (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.evaluate program (naiveEnv amt address) P31Ast.requires_naive_0 heap (context address)).Supported := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Execution.supported_of_finishes (naive_condition amt items heap address found).finishes

theorem naive.«Returns» (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (condition : HeapCalls.Condition program (naiveEnv amt address) P31Ast.requires_naive_0 heap (context address)) :
    (HeapCalls.call program "naive" [.scalar (.int amt)] heap (context address)).Returns := by
  obtain ⟨integers, found⟩ := Mutable.Value.ints_of_hasType typed
  have accepted : 0 ≤ amt ∧ ∀ c ∈ integers, 0 < c := by
    simpa using (naive_condition amt integers heap address found).condition_iff.mp condition
  obtain ⟨amount, items, rfl, positive, found⟩ := natural_inputs amt integers accepted.1 accepted.2 heap address found
  obtain ⟨extra, returned⟩ := naive.result (globals := context address) amount items positive heap address rfl found
  exact returned.returns

theorem naive.«Supported» (heap : Mutable.Heap) (amt : Int) (address : Nat)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (condition : HeapCalls.Condition program (naiveEnv amt address) P31Ast.requires_naive_0 heap (context address)) :
    (HeapCalls.call program "naive" [.scalar (.int amt)] heap (context address)).Supported :=
  (naive.«Returns» heap amt address valid typed condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p31
