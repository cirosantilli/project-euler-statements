import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p50.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.HeapCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p50
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := P50Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def numbers (items : List Int) : List Mutable.Value := items.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["primes_below", "prefix_sums", "sum_range", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

namespace primes_below
def values (limit : Nat) : List Nat := (List.range limit).filter fun n => decide (Nat.Prime n)
private def body (address : Nat) : List Stmt :=
  [.ifThen (.call (.name "is_prime") [.name "n"]) [.comprehensionAppend address (.name "n")] []]

private theorem loop (first count stop : Nat) (length : first + count = stop)
    (base : Mutable.Heap) (items : List Int) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "n" first stop 1 (body base.length) []]
      (base ++ [.list (numbers items)]) finalEnv
      (base ++ [.list (numbers (items ++ ((List.range' first count).filter fun n => decide (Nat.Prime n)).map Int.ofNat))]) := by
  induction count generalizing first items env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.filter_nil, List.map_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "n" (number first)
      have tested : Evaluates program bound (.call (.name "is_prime") [.name "n"])
          (base ++ [.list (numbers items)]) (flag (decide (Nat.Prime first)))
          (base ++ [.list (numbers items)]) := by
        apply Evaluates.call (values := [number first]) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil)
        exact (common.is_prime.heap_result first _).extend common_extension
      by_cases prime : Nat.Prime first
      · have emitted : BlockContinues program bound (body base.length)
            (base ++ [.list (numbers items)]) bound (base ++ [.list (numbers (items ++ [(first : Int)]))]) := by
          apply BlockContinues.branch (flag := true) tested (by simp [prime, Mutable.truth, scalarTruth])
          have looked : Evaluates program bound (.name "n")
              (ProjectEulerSolutions.HeapCollection.working base (numbers items) []) (number first)
              (ProjectEulerSolutions.HeapCollection.working base (numbers items) []) :=
            Evaluates.lookup (by simp [bound, setLocal])
          simpa only [ProjectEulerSolutions.HeapCollection.working, numbers, List.map_append,
            List.map_cons, List.map_nil, List.append_nil] using
            ProjectEulerSolutions.HeapCollection.emit base (numbers items) [] [] (number first)
              (by simpa only [List.append_nil] using looked)
        obtain ⟨finalEnv, rest⟩ := ih (first + 1) (by omega) (items ++ [(first : Int)]) bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, body,
          Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.filter_cons,
          show decide (Nat.Prime first) = true by simp [prime], if_true, List.map_cons,
          Int.natCast_add, Int.natCast_one, List.append_assoc, List.singleton_append] using emitted.append rest
      · have skipped : BlockContinues program bound (body base.length)
            (base ++ [.list (numbers items)]) bound (base ++ [.list (numbers items)]) :=
          BlockContinues.branch (flag := false) tested (by simp [prime, Mutable.truth, scalarTruth]) .nil
        obtain ⟨finalEnv, rest⟩ := ih (first + 1) (by omega) items bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, body,
          Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.filter_cons,
          show decide (Nat.Prime first) = false by simp [prime], Int.natCast_add,
          Int.natCast_one] using skipped.append rest

/-- Filtering the entire signed range terminates and allocates exactly one prime list. -/
theorem result (limit : Int) (heap : Mutable.Heap) :
    ReturnsValue program "primes_below" [number limit] heap (.ref heap.length)
      (heap ++ [.list (numbers ((values limit.toNat).map Int.ofNat))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases below : limit < 0
  · have empty : limit.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    apply Evaluates.list_comp_range (.cons (Evaluates.lookup rfl) .nil) rfl
    simp only [empty, values, List.range_zero, List.filter_nil, List.map_nil, numbers]
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  · lift limit to Nat using (by omega : 0 ≤ limit)
    obtain ⟨finalEnv, executed⟩ := loop 0 limit limit (by omega) heap [] _
    apply Evaluates.list_comp_range (finalEnv := finalEnv) (.cons (Evaluates.lookup rfl) .nil) rfl
    simpa only [numbers, values, Int.toNat_natCast, List.range_eq_range', List.nil_append, List.map_nil] using executed

theorem «Returns» (limit : Int) : (HeapCalls.call program "primes_below" [number limit] []).Returns :=
  (result limit []).returns

theorem «Supported» (limit : Int) : (HeapCalls.call program "primes_below" [number limit] []).Supported :=
  («Returns» limit).supported
end primes_below

namespace prefix_sums
def step (totals : List Int) (x : Int) : List Int := totals ++ [x + totals.getLast?.getD 0]
def values (items : List Int) : List Int := items.foldl step []

def fromTotal (total : Int) : List Int → List Int
  | [] => []
  | head :: tail => (total + head) :: fromTotal (total + head) tail

private theorem fold_values (items totals : List Int) :
    items.foldl step totals = totals ++ fromTotal (totals.getLast?.getD 0) items := by
  induction items generalizing totals with
  | nil => simp [fromTotal]
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp [step, fromTotal, List.getLast?_append, Int.add_comm, List.append_assoc]

theorem values_fromTotal (items : List Int) : values items = fromTotal 0 items := by
  simpa [values] using fold_values items []

theorem fromTotal_length (items : List Int) (total : Int) : (fromTotal total items).length = items.length := by
  induction items generalizing total with
  | nil => rfl
  | cons head tail ih => simpa [fromTotal] using ih (total + head)

theorem fromTotal_get (items : List Int) (total : Int) (position : Nat) (inside : position < items.length) :
    (fromTotal total items)[position]? = some (total + (items.take (position + 1)).sum) := by
  induction items generalizing total position with
  | nil => simp at inside
  | cons head tail ih =>
      cases position with
      | zero => simp [fromTotal]
      | succ position =>
          simpa [fromTotal, List.take_succ_cons, Int.add_assoc] using
            ih (total + head) position (by simpa using inside)

/-- Each output entry is the exact sum of the corresponding nonempty input prefix. -/
theorem values_get (items : List Int) (position : Nat) (inside : position < items.length) :
    (values items)[position]? = some ((items.take (position + 1)).sum) := by
  simpa only [values_fromTotal, zero_add] using fromTotal_get items 0 position inside

private def lastExpression : Expr :=
  .ifExp (.name "acc") (.subscript (.name "acc") (.unaryOp .uSub (.constant (.int 1)))) (.constant (.int 0))
private def body : List Stmt :=
  [.expr (.call (.attribute (.name "acc") "append") [.binOp (.name "x") .add lastExpression])]

private theorem last_result (totals : List Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (getAcc : env "acc" = some (.ref address)) (found : heap[address]? = some (.list (numbers totals))) :
    Evaluates program env lastExpression heap (number (totals.getLast?.getD 0)) heap := by
  by_cases empty : totals = []
  · subst totals
    apply Evaluates.conditional (flag := false) (Evaluates.lookup getAcc)
      (by simp [Mutable.truth, found, numbers]) Evaluates.constant
  · have positive : 0 < totals.length := List.length_pos_iff.mpr empty
    have selected : (numbers totals)[totals.length - 1]? = some (number (totals.getLast?.getD 0)) := by
      rw [numbers, List.getElem?_map, ← List.getLast?_eq_getElem?, List.getLast?_eq_some_getLast empty]
      rfl
    have adjusted : (-1 : Int) + (numbers totals).length = ((totals.length - 1 : Nat) : Int) := by
      simp only [numbers, List.length_map]
      omega
    have nonempty : numbers totals ≠ [] := by simpa [numbers] using empty
    apply Evaluates.conditional (flag := true) (Evaluates.lookup getAcc)
      (by simp [Mutable.truth, found, numbers, empty])
    apply Evaluates.subscript (middle := heap) (afterIndex := heap)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getAcc)
      (Evaluates.unary Evaluates.constant rfl)
    simp [Mutable.getItem, found, Mutable.index, adjusted, nonempty, selected, Except.map]

private theorem loop (items remaining : List Int) (position : Nat) (suffix : items.drop position = remaining)
    (base : Mutable.Heap) (address : Nat) (found : base[address]? = some (.list (numbers items)))
    (totals : List Int) (env : HeapCalls.Env) (getAcc : env "acc" = some (.ref base.length)) :
    ∃ finalEnv, BlockContinues program env [.sequenceStepLoop "x" (.ref address) position body []]
      (ProjectEulerSolutions.HeapCollection.working base (numbers totals) []) finalEnv
      (ProjectEulerSolutions.HeapCollection.working base (numbers (remaining.foldl step totals)) []) ∧
      finalEnv "acc" = some (.ref base.length) := by
  induction remaining generalizing position totals env with
  | nil =>
      refine ⟨env, ?_, getAcc⟩
      apply BlockContinues.sequence_done (items := numbers items)
        (by simp [sequenceValue, Mutable.sequence,
          ProjectEulerSolutions.HeapCollection.working,
          ProjectEulerSolutions.HeapCollection.prefix_found base _ address _ found])
      · have missing : items[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        simp [numbers, missing]
      · exact .nil
  | cons head tail ih =>
      let bound := setLocal env "x" (number head)
      let heap := ProjectEulerSolutions.HeapCollection.working base (numbers totals) []
      have getAcc' : bound "acc" = some (.ref base.length) := by simpa [bound, setLocal] using getAcc
      have accFound : heap[base.length]? = some (.list (numbers totals)) := by simp [heap, ProjectEulerSolutions.HeapCollection.found]
      have next : Evaluates program bound (.binOp (.name "x") .add lastExpression) heap
          (number (head + totals.getLast?.getD 0)) heap :=
        Evaluates.binary (av := number head) (bv := number (totals.getLast?.getD 0))
          (Evaluates.lookup (by simp [bound, setLocal]))
          (last_result totals heap bound base.length getAcc' accFound) rfl
      have appended : BlockContinues program bound body heap bound
          (ProjectEulerSolutions.HeapCollection.working base (numbers (step totals head)) []) := by
        have evaluated := Evaluates.append (Evaluates.lookup getAcc') accFound next accFound
        apply BlockContinues.discard
        simpa only [heap, step, numbers, List.map_append, List.map_cons, List.map_nil,
          ProjectEulerSolutions.HeapCollection.store] using evaluated
      obtain ⟨finalEnv, rest, finalAcc⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (step totals head) bound getAcc'
      refine ⟨finalEnv, ?_, finalAcc⟩
      have selected : items[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      apply BlockContinues.sequence_step (source := .ref address) (items := numbers items) (value := number head)
        (by simp [sequenceValue, Mutable.sequence, ProjectEulerSolutions.HeapCollection.working,
          ProjectEulerSolutions.HeapCollection.prefix_found base _ address _ found]) (by simp [numbers, selected])
      simpa only [Calls.loopContinuation, show Calls.loopControl body = false from rfl,
        Bool.false_eq_true, if_false, List.foldl_cons, heap] using appended.append rest

/-- The output is fresh; even shared input lists retain every element and their identity. -/
theorem result (items : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "prefix_sums" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (numbers (values items))]) := by
  let initial := functionEnv ((findFunctionIn program.body "prefix_sums").getD ([], [])).1
    ((findFunctionIn program.body "prefix_sums").getD ([], [])).2 [.ref address] []
  let ready := setLocal initial "acc" (.ref heap.length)
  obtain ⟨finalEnv, scanned, finalAcc⟩ := loop items items 0 rfl heap address found [] ready rfl
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  have scanned' : BlockContinues program ready [.forIn (.name "x") (.name "xs") body []]
      (heap ++ [.list []]) finalEnv (heap ++ [.list (numbers (values items))]) := by
    apply BlockContinues.for_sequence (value := .ref address) (items := numbers items)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup (show ready "xs" = some (.ref address) from rfl))
      (by simp [Mutable.sequence, ProjectEulerSolutions.HeapCollection.prefix_found heap _ address _ found])
    simpa only [ProjectEulerSolutions.HeapCollection.working, numbers, List.map_nil, values] using scanned
  apply scanned'.returns
  exact BlockReturns.return_value (Evaluates.lookup finalAcc)

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "prefix_sums" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (result items heap address found).returns

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "prefix_sums" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported
end prefix_sums

namespace sum_range
def entry (items : List Int) (position : Int) : Int :=
  if 0 ≤ position ∧ position < items.length then (items[position.toNat]?).getD 0 else 0
def value (items : List Int) (i j : Int) : Int :=
  if i = 0 then entry items (j - 1) else entry items (j - 1) - entry items (i - 1)

theorem entry_values (items : List Int) (stop : Nat) (inside : stop ≤ items.length) :
    entry (prefix_sums.values items) ((stop : Int) - 1) = (items.take stop).sum := by
  cases stop with
  | zero => simp [entry]
  | succ stop =>
      have size : (prefix_sums.values items).length = items.length := by
        rw [prefix_sums.values_fromTotal, prefix_sums.fromTotal_length]
      have bounded : 0 ≤ ((stop + 1 : Nat) : Int) - 1 ∧
          ((stop + 1 : Nat) : Int) - 1 < (prefix_sums.values items).length := by
        rw [size]
        omega
      have index : (((stop + 1 : Nat) : Int) - 1).toNat = stop := by omega
      simp only [entry, if_pos bounded, index, prefix_sums.values_get items stop (by omega), Option.getD_some]

/-- On a valid half-open interval the guarded source subtraction is exactly its input sum. -/
theorem value_prefix (items : List Int) (first stop : Nat) (ordered : first ≤ stop) (inside : stop ≤ items.length) :
    value (prefix_sums.values items) first stop = ((items.drop first).take (stop - first)).sum := by
  have lower : first ≤ items.length := by omega
  have difference : (items.take stop).sum - (items.take first).sum =
      ((items.drop first).take (stop - first)).sum := by
    have split := congrArg List.sum (List.take_append_drop first (items.take stop))
    simp only [List.sum_append, List.take_take, Nat.min_eq_left ordered, List.drop_take] at split
    omega
  unfold value
  rw [entry_values items stop inside, entry_values items first lower]
  by_cases zero : first = 0
  · subst first
    simp
  · simpa [zero] using difference

private def entryExpression (index : Expr) : Expr :=
  .ifExp (.compare (.constant (.int 0)) [(.ltE, index), (.lt, .builtinCall .len [.name "pref"])])
    (.subscript (.name "pref") index) (.constant (.int 0))

private theorem entry_result (items : List Int) (position : Int) (expression : Expr)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (getPref : env "pref" = some (.ref address)) (found : heap[address]? = some (.list (numbers items)))
    (ordinary : ∀ a b c, expression ≠ .slice a b c)
    (evaluated : Evaluates program env expression heap (number position) heap) :
    Evaluates program env (entryExpression expression) heap (number (entry items position)) heap := by
  have sized : Evaluates program env (.builtinCall .len [.name "pref"]) heap (number items.length) heap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getPref) .nil)
    simp [primitive, Mutable.length, found, numbers]
  have tested : Evaluates program env
      (.compare (.constant (.int 0)) [(.ltE, expression), (.lt, .builtinCall .len [.name "pref"])])
      heap (flag (decide (0 ≤ position ∧ position < items.length))) heap := by
    apply Evaluates.chain Evaluates.constant
    by_cases lower : 0 ≤ position
    · apply Evaluates.Compares.next (compared := flag true) (middle := heap) (afterComparison := heap) evaluated
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]) rfl
      apply Evaluates.Compares.last sized
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · apply Evaluates.Compares.stop evaluated
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower])
        (by simp [lower, Mutable.truth, scalarTruth])
  by_cases bounded : 0 ≤ position ∧ position < items.length
  · have inside : position.toNat < items.length := by omega
    have actual : (numbers items)[position.toNat]'(by simpa [numbers] using inside) = number (entry items position) := by
      simp [numbers, entry, bounded]
    have position_cast : (position.toNat : Int) = position := by omega
    apply Evaluates.conditional (flag := true) tested (by simp [bounded, Mutable.truth, scalarTruth])
    apply Evaluates.subscript (middle := heap) (afterIndex := heap)
      ordinary (Evaluates.lookup getPref) evaluated
    simpa only [position_cast, actual] using Mutable.getItem_list heap address position.toNat (numbers items) found
      (by simpa [numbers] using inside)
  · apply Evaluates.conditional (flag := false) tested (by simp [bounded, Mutable.truth, scalarTruth])
    simpa only [entry, if_neg bounded] using (Evaluates.constant (module := program) (env := env) (heap := heap)
      (value := Constant.int 0))

/-- Guarded reads handle arbitrary signed indices without changing the prefix list. -/
theorem result (items : List Int) (i j : Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "sum_range" [.ref address, number i, number j] heap (number (value items i j)) heap := by
  let initial := functionEnv ((findFunctionIn program.body "sum_range").getD ([], [])).1
    ((findFunctionIn program.body "sum_range").getD ([], [])).2 [.ref address, number i, number j] []
  have index_result (name : String) (index : Int) (getIndex : initial name = some (number index)) :
      Evaluates program initial (.binOp (.name name) .sub (.constant (.int 1))) heap (number (index - 1)) heap :=
    Evaluates.binary (Evaluates.lookup getIndex) Evaluates.constant rfl
  have right := entry_result items (j - 1) (.binOp (.name "j") .sub (.constant (.int 1))) heap initial address
    rfl found (by intros; intro impossible; cases impossible) (index_result "j" j rfl)
  have left := entry_result items (i - 1) (.binOp (.name "i") .sub (.constant (.int 1))) heap initial address
    rfl found (by intros; intro impossible; cases impossible) (index_result "i" i rfl)
  have tested : Evaluates program initial (.compare (.name "i") [(.eq, .constant (.int 0))]) heap
      (flag (decide (i = 0))) heap :=
    Evaluates.compare (av := number i) (bv := number 0) (Evaluates.lookup rfl) Evaluates.constant rfl
  apply BlockReturns.function rfl rfl
  by_cases zero : i = 0
  · simp only [value, if_pos zero]
    apply BlockReturns.branch (flag := true) tested (by simp [zero, Mutable.truth, scalarTruth])
    exact BlockReturns.return_value right
  · simp only [value, if_neg zero]
    apply BlockReturns.branch (flag := false) tested (by simp [zero, Mutable.truth, scalarTruth])
    exact BlockReturns.return_value (Evaluates.binary right left rfl)

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (i j : Int) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sum_range" [.ref address, number i, number j] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (result items i j heap address found).returns

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (i j : Int) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sum_range" [.ref address, number i, number j] heap).Supported :=
  («Returns» heap address i j valid typed).supported
end sum_range
end data.«project-euler-statements».data.py.project_euler_statements.p50
