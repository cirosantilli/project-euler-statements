import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p50.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.ConsecutivePrimeSums
import ProjectEulerStatements.Lib.ArgMaximum

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

namespace naive
open ProjectEulerSolutions.ConsecutivePrimeSums
open ProjectEulerSolutions.HeapCollection
private def code : List Stmt := executableBody ((findFunctionIn program.body "naive").getD ([], [])).2
private def rowBody : List Stmt := match (code[3]? : Option Stmt) with
  | some (.forIn _ _ body _) => body | _ => []
private def cellBody : List Stmt := match (rowBody[0]? : Option Stmt) with
  | some (.forIn _ _ body _) => body | _ => []
private def acceptedBody : List Stmt := match (cellBody[0]? : Option Stmt) with
  | some (.ifThen _ body _) => body | _ => []
private def appendBody : List Stmt := match (acceptedBody[1]? : Option Stmt) with
  | some (.ifThen _ body _) => body | _ => []
private def pairValues (items : List Nat) (candidate : Window) : List Mutable.Value :=
  [number candidate.length, number (window items candidate.first candidate.length)]
private def refs (addresses : List Nat) : List Mutable.Value := addresses.map Mutable.Value.ref
private def integers (items : List Nat) : List Int := items.map Int.ofNat

private theorem sum_integers (items : List Nat) : (integers items).sum = (items.sum : Int) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [integers, List.sum_cons, ← ih]

private def cell (items : List Nat) (limit first stop : Nat) : List Window :=
  if first < stop ∧ window items first (stop - first) < limit ∧ Nat.Prime (window items first (stop - first)) then
    [⟨first, stop - first⟩] else []
private def rowFrom (items : List Nat) (limit first start count : Nat) : List Window :=
  (List.range' start count).flatMap (cell items limit first)
private def rowsFrom (items : List Nat) (limit start count : Nat) : List Window :=
  (List.range' start count).flatMap (fun first => rowFrom items limit first 0 (items.length + 1))

private theorem valid_cell (items : List Nat) (limit first stop : Nat) (bounded : stop ≤ items.length) :
    Valid items limit ⟨first, stop - first⟩ ↔
      first < stop ∧ window items first (stop - first) < limit ∧ Nat.Prime (window items first (stop - first)) := by
  change (0 < stop - first ∧ first + (stop - first) ≤ items.length ∧
    window items first (stop - first) < limit ∧ Nat.Prime (window items first (stop - first))) ↔ _
  constructor
  · rintro ⟨positive, _, below, prime⟩
    exact ⟨by omega, below, prime⟩
  · rintro ⟨ordered, below, prime⟩
    exact ⟨by omega, by omega, below, prime⟩

private theorem rowFrom_full (items : List Nat) (limit first : Nat) :
    rowFrom items limit first 0 (items.length + 1) = row items limit first := by
  have collect (stops : List Nat) (bounded : ∀ stop ∈ stops, stop ≤ items.length) :
      stops.flatMap (cell items limit first) =
        (stops.map (fun stop => Window.mk first (stop - first))).filter (fun candidate => decide (Valid items limit candidate)) := by
    induction stops with
    | nil => rfl
    | cons stop tail ih =>
        have within := bounded stop (by simp)
        have rest := ih (by intro value member; exact bounded value (by simp [member]))
        by_cases valid : Valid items limit ⟨first, stop - first⟩
        · have accepted := (valid_cell items limit first stop within).mp valid
          simp [cell, accepted, valid, rest]
        · have rejected : ¬ (first < stop ∧ window items first (stop - first) < limit ∧ Nat.Prime (window items first (stop - first))) :=
            fun accepted => valid ((valid_cell items limit first stop within).mpr accepted)
          simp [cell, rejected, valid, rest]
  unfold rowFrom row
  rw [← List.range_eq_range']
  exact collect _ (by intro stop member; have := List.mem_range.mp member; omega)

private theorem rowsFrom_full (items : List Nat) (limit : Nat) :
    rowsFrom items limit 0 (items.length + 1) = candidates items limit := by
  simp only [rowsFrom, rowFrom_full, ← List.range_eq_range', candidates]

private structure Inputs (base : Mutable.Heap) (items : List Nat) (primeAddress prefixAddress : Nat) : Prop where
  primes : base[primeAddress]? = some (.list (numbers (integers items)))
  prefixSums : base[prefixAddress]? = some (.list (numbers (prefix_sums.values (integers items))))

private structure Locals (env : HeapCalls.Env) (limit : Int) (collector primeAddress prefixAddress : Nat) : Prop where
  getLimit : env "limit" = some (number limit)
  getCandidates : env "candidates" = some (.ref collector)
  getPrimes : env "ps" = some (.ref primeAddress)
  getPrefix : env "pref" = some (.ref prefixAddress)

private theorem Locals.set (locals : Locals env limit collector primeAddress prefixAddress) (name : String) (value : Mutable.Value)
    (unused : name ∉ ["limit", "candidates", "ps", "pref"]) :
    Locals (setLocal env name value) limit collector primeAddress prefixAddress := by
  have stable (query : String) (member : query ∈ ["limit", "candidates", "ps", "pref"]) :
      setLocal env name value query = env query := by
    have different : query ≠ name := by intro same; subst query; exact unused member
    simp [setLocal, different]
  exact ⟨(stable "limit" (by simp)).trans locals.getLimit, (stable "candidates" (by simp)).trans locals.getCandidates,
    (stable "ps" (by simp)).trans locals.getPrimes, (stable "pref" (by simp)).trans locals.getPrefix⟩

private def Rows (heap : Mutable.Heap) (items : List Nat) (collector : Nat) (addresses : List Nat) (windows : List Window) : Prop :=
  List.Forall₂ (fun address candidate => collector < address ∧ heap[address]? = some (.tuple (pairValues items candidate))) addresses windows

private theorem Rows.change (rows : Rows (working base old garbage) items base.length addresses windows)
    (replacement : List Mutable.Value) (extra : Mutable.Heap) :
    Rows (working base replacement (garbage ++ extra)) items base.length addresses windows := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons ⟨head.1, other_found base old replacement garbage extra _ _ (by omega) head.2⟩ ih

private theorem sum_result (items : List Nat) (first stop prefixAddress : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (ordered : first ≤ stop) (bounded : stop ≤ items.length)
    (getPrefix : env "pref" = some (.ref prefixAddress)) (getI : env "i" = some (number first)) (getJ : env "j" = some (number stop))
    (found : heap[prefixAddress]? = some (.list (numbers (prefix_sums.values (integers items))))) :
    Evaluates program env (.call (.name "sum_range") [.name "pref", .name "i", .name "j"]) heap
      (number (window items first (stop - first))) heap := by
  have exactValue := sum_range.value_prefix (integers items) first stop ordered (by simpa [integers] using bounded)
  have converted : sum_range.value (prefix_sums.values (integers items)) first stop = (window items first (stop - first) : Int) := by
    rw [exactValue]
    simpa only [integers, List.map_drop, List.map_take, window] using sum_integers ((items.drop first).take (stop - first))
  apply Evaluates.call (values := [.ref prefixAddress, number first, number stop])
    (.cons (Evaluates.lookup getPrefix) (.cons (Evaluates.lookup getI) (.cons (Evaluates.lookup getJ) .nil)))
  simpa only [converted] using sum_range.result (prefix_sums.values (integers items)) first stop heap prefixAddress found

private theorem accepted_result (value : Nat) (limit : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getValue : env "s" = some (number value)) (getLimit : env "limit" = some (number limit)) :
    Evaluates program env (.boolOp .and [.compare (.name "s") [(.lt, .name "limit")], .call (.name "is_prime") [.name "s"]])
      heap (flag (decide (value < limit.toNat ∧ Nat.Prime value))) heap := by
  have below_equiv : (value : Int) < limit ↔ value < limit.toNat := by omega
  have tested : Evaluates program env (.compare (.name "s") [(.lt, .name "limit")]) heap (flag (decide (value < limit.toNat))) heap :=
    Evaluates.compare (Evaluates.lookup getValue) (Evaluates.lookup getLimit)
      (by
        change (some (Except.ok (flag (decide ((value : Int) < limit))), heap) :
          Option (Except ExceptionObject Mutable.Value × Mutable.Heap)) = _
        simp only [below_equiv])
  by_cases below : value < limit.toNat
  · simp only [below, true_and]
    apply Evaluates.boolean_next (by simpa only [below, decide_true] using tested) rfl rfl
    apply Evaluates.boolean_last (flag := decide (Nat.Prime value))
    · apply Evaluates.call (values := [number value]) (.cons (Evaluates.lookup getValue) .nil)
      exact (common.is_prime.heap_result value heap).extend common_extension
    · rfl
  · simp only [below, false_and, decide_false]
    exact Evaluates.boolean_stop (by simpa only [below, decide_false] using tested) rfl rfl

private theorem append_candidate (items : List Nat) (first stop : Nat) (ordered : first ≤ stop)
    (base : Mutable.Heap) (garbage : Mutable.Heap) (addresses : List Nat) (windows : List Window) (env : HeapCalls.Env)
    (getCandidates : env "candidates" = some (.ref base.length)) (getI : env "i" = some (number first))
    (getJ : env "j" = some (number stop)) (getSum : env "s" = some (number (window items first (stop - first))))
    (rows : Rows (working base (refs addresses) garbage) items base.length addresses windows) :
    ∃ extra, BlockContinues program env appendBody (working base (refs addresses) garbage) env
        (working base (refs (addresses ++ [(working base (refs addresses) garbage).length])) (garbage ++ extra)) ∧
      Rows (working base (refs (addresses ++ [(working base (refs addresses) garbage).length])) (garbage ++ extra))
        items base.length (addresses ++ [(working base (refs addresses) garbage).length]) (windows ++ [⟨first, stop - first⟩]) := by
  let heap := working base (refs addresses) garbage
  let candidate : Window := ⟨first, stop - first⟩
  let newAddresses := addresses ++ [heap.length]
  let extra : Mutable.Heap := [.tuple (pairValues items candidate)]
  have created : Evaluates program env (.tuple [.binOp (.name "j") .sub (.name "i"), .name "s"]) heap (.ref heap.length) (heap ++ extra) := by
    apply Evaluates.tuple (values := pairValues items candidate)
      (.cons (Evaluates.binary (av := number stop) (bv := number first) (middle := heap) (afterRight := heap)
        (Evaluates.lookup getJ) (Evaluates.lookup getI) (by simp [candidate, Mutable.binary, scalarBinary, Int.natCast_sub ordered]))
        (.cons (Evaluates.lookup getSum) .nil)) (by simp [pairValues])
  have listFound : heap[base.length]? = some (.list (refs addresses)) := by simp [heap, found]
  have afterList : (heap ++ extra)[base.length]? = some (.list (refs addresses)) := prefix_found heap extra _ _ listFound
  have emitted : BlockContinues program env appendBody heap env (working base (refs newAddresses) (garbage ++ extra)) := by
    apply BlockContinues.discard
    have evaluated := Evaluates.append (Evaluates.lookup getCandidates) listFound created afterList
    simpa only [heap, ProjectEulerSolutions.HeapCollection.append, store, newAddresses, refs, List.map_append,
      List.map_cons, List.map_nil] using evaluated
  have previous := rows.change (refs newAddresses) extra
  have fresh : base.length < heap.length ∧
      (working base (refs newAddresses) (garbage ++ extra))[heap.length]? = some (.tuple (pairValues items candidate)) := by
    refine ⟨by simp [heap, working], ?_⟩
    have allocated : (heap ++ extra)[heap.length]? = some (.tuple (pairValues items candidate)) := by simp [extra]
    have updated := List.getElem?_set_ne (l := heap ++ extra) (a := Mutable.Object.list (refs newAddresses))
      (show base.length ≠ heap.length by simp [heap, working])
    simpa only [heap, ProjectEulerSolutions.HeapCollection.append, store] using updated.trans allocated
  exact ⟨extra, emitted, List.rel_append previous (.cons fresh .nil)⟩

/-- One source cell either appends its fresh candidate or leaves the list and heap unchanged. -/
private theorem cell_result (items : List Nat) (limit : Int) (first stop primeAddress prefixAddress : Nat) (bounded : stop ≤ items.length)
    (base garbage : Mutable.Heap) (inputs : Inputs base items primeAddress prefixAddress)
    (addresses : List Nat) (windows : List Window) (env : HeapCalls.Env)
    (locals : Locals env limit base.length primeAddress prefixAddress)
    (getI : env "i" = some (number first)) (getJ : env "j" = some (number stop))
    (rows : Rows (working base (refs addresses) garbage) items base.length addresses windows) :
    ∃ finalEnv finalAddresses extra,
      BlockContinues program env cellBody (working base (refs addresses) garbage) finalEnv
        (working base (refs finalAddresses) (garbage ++ extra)) ∧
      Rows (working base (refs finalAddresses) (garbage ++ extra)) items base.length finalAddresses (windows ++ cell items limit.toNat first stop) ∧
      Locals finalEnv limit base.length primeAddress prefixAddress ∧
      (∀ name, name ≠ "s" → finalEnv name = env name) := by
  let heap := working base (refs addresses) garbage
  have orderedTest : Evaluates program env (.compare (.name "i") [(.lt, .name "j")]) heap
      (flag (decide (first < stop))) heap :=
    Evaluates.compare (Evaluates.lookup getI) (Evaluates.lookup getJ) (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases ordered : first < stop
  · let ready := setLocal env "s" (number (window items first (stop - first)))
    have readyLocals := locals.set "s" (number (window items first (stop - first))) (by simp)
    have getSum : ready "s" = some (number (window items first (stop - first))) := by simp [ready, setLocal]
    have assigned : BlockContinues program env [acceptedBody[0]'(by decide)] heap ready heap := by
      apply BlockContinues.assign
      apply sum_result items first stop prefixAddress heap env (by omega) bounded locals.getPrefix getI getJ
      simp [heap, working, prefix_found base _ _ _ inputs.prefixSums]
    have accepted := accepted_result (window items first (stop - first)) limit heap ready getSum readyLocals.getLimit
    by_cases valid : window items first (stop - first) < limit.toNat ∧ Nat.Prime (window items first (stop - first))
    · obtain ⟨extra, emitted, finalRows⟩ := append_candidate items first stop (by omega) base garbage addresses windows ready
        readyLocals.getCandidates (by simpa [ready, setLocal] using getI) (by simpa [ready, setLocal] using getJ) getSum rows
      refine ⟨ready, addresses ++ [heap.length], extra, ?_, ?_, readyLocals, ?_⟩
      · apply BlockContinues.branch (flag := true) orderedTest (by simp [ordered, Mutable.truth, scalarTruth])
        apply assigned.append
        exact BlockContinues.branch (flag := true) accepted (by simp only [valid]; rfl) emitted
      · simpa only [cell, if_pos (And.intro ordered valid)] using finalRows
      · intro name different
        simp [ready, setLocal, different]
    · refine ⟨ready, addresses, [], ?_, ?_, readyLocals, ?_⟩
      · simp only [List.append_nil]
        apply BlockContinues.branch (flag := true) orderedTest (by simp [ordered, Mutable.truth, scalarTruth])
        apply assigned.append
        exact BlockContinues.branch (flag := false) accepted (by simp only [valid, decide_false]; rfl) .nil
      · have rejected : ¬ (first < stop ∧ window items first (stop - first) < limit.toNat ∧ Nat.Prime (window items first (stop - first))) :=
          fun accepted => valid accepted.2
        simpa only [cell, if_neg rejected, List.append_nil] using rows
      · intro name different
        simp [ready, setLocal, different]
  · refine ⟨env, addresses, [], ?_, ?_, locals, fun _ _ => rfl⟩
    · simp only [List.append_nil]
      exact BlockContinues.branch (flag := false) orderedTest (by simp [ordered, Mutable.truth, scalarTruth]) .nil
    · simpa [cell, ordered] using rows

private theorem inner_loop (items : List Nat) (limit : Int) (first start count primeAddress prefixAddress : Nat)
    (endpoint : start + count = items.length + 1) (base garbage : Mutable.Heap)
    (inputs : Inputs base items primeAddress prefixAddress) (addresses : List Nat) (windows : List Window) (env : HeapCalls.Env)
    (locals : Locals env limit base.length primeAddress prefixAddress) (getI : env "i" = some (number first))
    (rows : Rows (working base (refs addresses) garbage) items base.length addresses windows) :
    ∃ finalEnv finalAddresses extra,
      BlockContinues program env [.rangeStepLoop "j" start (items.length + 1) 1 cellBody []]
        (working base (refs addresses) garbage) finalEnv (working base (refs finalAddresses) (garbage ++ extra)) ∧
      Rows (working base (refs finalAddresses) (garbage ++ extra)) items base.length finalAddresses
        (windows ++ rowFrom items limit.toNat first start count) ∧
      Locals finalEnv limit base.length primeAddress prefixAddress ∧ finalEnv "i" = some (number first) := by
  induction count generalizing start garbage addresses windows env with
  | zero =>
      refine ⟨env, addresses, [], ?_, ?_, locals, getI⟩
      · simp only [List.append_nil]
        exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
      · simpa [rowFrom] using rows
  | succ count ih =>
      let bound := setLocal env "j" (number start)
      have boundLocals : Locals bound limit base.length primeAddress prefixAddress := locals.set "j" (number start) (by simp)
      have getI' : bound "i" = some (number first) := by simpa [bound, setLocal] using getI
      obtain ⟨middleEnv, middleAddresses, allocated, stepped, middleRows, middleLocals, stable⟩ :=
        cell_result items limit first start primeAddress prefixAddress (by omega) base garbage inputs addresses windows bound
          boundLocals getI' (by simp [bound, setLocal]) rows
      obtain ⟨finalEnv, finalAddresses, extra, scanned, finalRows, finalLocals, finalI⟩ :=
        ih (start + 1) (by omega) (garbage ++ allocated) middleAddresses (windows ++ cell items limit.toNat first start)
          middleEnv middleLocals ((stable "i" (by decide)).trans getI') middleRows
      refine ⟨finalEnv, finalAddresses, allocated ++ extra, ?_, ?_, finalLocals, finalI⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl cellBody = false from rfl, Bool.false_eq_true,
          if_false, Int.natCast_add, Int.natCast_one, List.append_assoc] using stepped.append scanned
      · simpa only [rowFrom, List.range'_succ, List.flatMap_cons, List.append_assoc] using finalRows

private theorem bound_result (items : List Nat) (limit : Int) (primeAddress prefixAddress : Nat) (base garbage : Mutable.Heap)
    (inputs : Inputs base items primeAddress prefixAddress) (addresses : List Nat) (env : HeapCalls.Env)
    (locals : Locals env limit base.length primeAddress prefixAddress) :
    Evaluates program env (.binOp (.builtinCall .len [.name "ps"]) .add (.constant (.int 1)))
      (working base (refs addresses) garbage) (number (items.length + 1 : Nat)) (working base (refs addresses) garbage) := by
  apply Evaluates.binary (av := number items.length) (bv := number 1)
    (middle := working base (refs addresses) garbage) (afterRight := working base (refs addresses) garbage)
  · apply Evaluates.builtin (.cons (Evaluates.lookup locals.getPrimes) .nil)
    simp [primitive, Mutable.length, working, prefix_found base _ _ _ inputs.primes, numbers, integers]
  · exact Evaluates.constant
  · simp [Mutable.binary, scalarBinary]

private theorem outer_loop (items : List Nat) (limit : Int) (start count primeAddress prefixAddress : Nat)
    (endpoint : start + count = items.length + 1) (base garbage : Mutable.Heap)
    (inputs : Inputs base items primeAddress prefixAddress) (addresses : List Nat) (windows : List Window) (env : HeapCalls.Env)
    (locals : Locals env limit base.length primeAddress prefixAddress)
    (rows : Rows (working base (refs addresses) garbage) items base.length addresses windows) :
    ∃ finalEnv finalAddresses extra,
      BlockContinues program env [.rangeStepLoop "i" start (items.length + 1) 1 rowBody []]
        (working base (refs addresses) garbage) finalEnv (working base (refs finalAddresses) (garbage ++ extra)) ∧
      Rows (working base (refs finalAddresses) (garbage ++ extra)) items base.length finalAddresses
        (windows ++ rowsFrom items limit.toNat start count) ∧
      Locals finalEnv limit base.length primeAddress prefixAddress := by
  induction count generalizing start garbage addresses windows env with
  | zero =>
      refine ⟨env, addresses, [], ?_, ?_, locals⟩
      · simp only [List.append_nil]
        exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
      · simpa [rowsFrom] using rows
  | succ count ih =>
      let bound := setLocal env "i" (number start)
      have boundLocals : Locals bound limit base.length primeAddress prefixAddress := locals.set "i" (number start) (by simp)
      obtain ⟨middleEnv, middleAddresses, allocated, iterated, middleRows, middleLocals, getI⟩ :=
        inner_loop items limit start 0 (items.length + 1) primeAddress prefixAddress (by omega) base garbage inputs addresses windows
          bound boundLocals (by simp [bound, setLocal]) rows
      have rowRun : BlockContinues program bound rowBody (working base (refs addresses) garbage) middleEnv
          (working base (refs middleAddresses) (garbage ++ allocated)) := by
        apply BlockContinues.for_range (values := [number (items.length + 1 : Nat)])
          (.cons (bound_result items limit primeAddress prefixAddress base garbage inputs addresses bound boundLocals) .nil) rfl
        exact iterated
      obtain ⟨finalEnv, finalAddresses, extra, scanned, finalRows, finalLocals⟩ :=
        ih (start + 1) (by omega) (garbage ++ allocated) middleAddresses
          (windows ++ rowFrom items limit.toNat start 0 (items.length + 1)) middleEnv middleLocals middleRows
      refine ⟨finalEnv, finalAddresses, allocated ++ extra, ?_, ?_, finalLocals⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl rowBody = false from rfl, Bool.false_eq_true,
          if_false, Int.natCast_add, Int.natCast_one, List.append_assoc] using rowRun.append scanned
      · simpa only [rowsFrom, List.range'_succ, List.flatMap_cons, List.append_assoc] using finalRows

/-- Both exhaustive source ranges collect exactly the mathematical candidates, in the same order. -/
theorem enumerate (items : List Nat) (limit : Int) (primeAddress prefixAddress : Nat) (base : Mutable.Heap) (env : HeapCalls.Env)
    (inputs : Inputs base items primeAddress prefixAddress) (locals : Locals env limit base.length primeAddress prefixAddress) :
    ∃ finalEnv finalAddresses garbage,
      BlockContinues program env [code[3]'(by decide)] (base ++ [.list []]) finalEnv (working base (refs finalAddresses) garbage) ∧
      Rows (working base (refs finalAddresses) garbage) items base.length finalAddresses (candidates items limit.toNat) ∧
      Locals finalEnv limit base.length primeAddress prefixAddress := by
  obtain ⟨finalEnv, finalAddresses, garbage, scanned, rows, finalLocals⟩ := outer_loop items limit 0 (items.length + 1)
    primeAddress prefixAddress (by omega) base [] inputs [] [] env locals .nil
  refine ⟨finalEnv, finalAddresses, garbage, ?_, ?_, finalLocals⟩
  · apply BlockContinues.for_range (values := [number (items.length + 1 : Nat)])
      (.cons (bound_result items limit primeAddress prefixAddress base [] inputs [] env locals) .nil) rfl
    simpa only [working, refs, List.map_nil, List.append_nil] using scanned
  · simpa only [List.nil_append, List.append_nil, rowsFrom_full] using rows

private def keyExpression : Expr := .subscript (.name "p") (.constant (.int 0))
private def maximumExpression : Expr := .extremumSequence true (.name "candidates") "p" keyExpression
private def selectionExpression : Expr :=
  .ifExp (.name "candidates") (.subscript maximumExpression (.constant (.int 1))) (.constant (.int 0))
private abbrev cursor (env : HeapCalls.Env) (collector : Nat) : SequenceExtremum :=
  ⟨true, .ref collector, "p", keyExpression, env⟩

private theorem key_result (items : List Nat) (candidate : Window) (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (getP : env "p" = some (.ref address)) (found : heap[address]? = some (.tuple (pairValues items candidate))) :
    Evaluates program env keyExpression heap (number candidate.length) heap := by
  apply Evaluates.subscript (middle := heap) (afterIndex := heap)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getP) Evaluates.constant
  simp [Mutable.getItem, found, pairValues, Mutable.index, Except.map]

private theorem maximum_loop (items : List Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (collector : Nat)
    (all : List Nat) (position : Nat) (remaining : List Nat) (windows : List Window)
    (found : heap[collector]? = some (.list (refs all))) (suffix : all.drop position = remaining)
    (rows : Rows heap items collector remaining windows) (bestAddress : Nat) (best : Window)
    (bestFound : heap[bestAddress]? = some (.tuple (pairValues items best))) :
    ∃ address, ExtremumReturns program (cursor env collector) position (some (.ref bestAddress, number best.length))
        heap (.ref address) heap ∧
      heap[address]? = some (.tuple (pairValues items (windows.foldl (ProjectEulerStatements.ArgMaximum.select Window.length) best))) := by
  induction rows generalizing position bestAddress best with
  | nil =>
      refine ⟨bestAddress, ExtremumReturns.done ?_, bestFound⟩
      have missing : all[position]? = none := by simpa [suffix] using (List.head?_drop (l := all) (i := position)).symm
      simp [extremumItem, Mutable.sequence, found, refs, missing]
  | @cons address candidate addresses windows head tail ih =>
      have selected : all[position]? = some address := by simpa [suffix] using (List.head?_drop (l := all) (i := position)).symm
      have nextSuffix : all.drop (position + 1) = addresses := by simp [List.drop_add_one_eq_tail_drop, suffix]
      have read : extremumItem (.ref collector) position heap = some (.ok (some (.ref address)), heap) := by
        simp [extremumItem, Mutable.sequence, found, refs, selected]
      have key := key_result items candidate heap (setLocal env "p" (.ref address)) address rfl head.2
      by_cases better : best.length < candidate.length
      · obtain ⟨winner, rest, finalFound⟩ := ih (position + 1) nextSuffix address candidate head.2
        refine ⟨winner, ExtremumReturns.next read key ?_ rest, ?_⟩
        · simp [SequenceExtremum.choose, HeapCalls.compare, scalarCompare, evalCmpOp, Mutable.truth, scalarTruth, better, Except.map]
        · simpa [ProjectEulerStatements.ArgMaximum.select, better] using finalFound
      · obtain ⟨winner, rest, finalFound⟩ := ih (position + 1) nextSuffix bestAddress best bestFound
        refine ⟨winner, ExtremumReturns.next read key ?_ rest, ?_⟩
        · simp [SequenceExtremum.choose, HeapCalls.compare, scalarCompare, evalCmpOp, Mutable.truth, scalarTruth, better, Except.map]
        · simpa [ProjectEulerStatements.ArgMaximum.select, better] using finalFound

private theorem maximum_result (items : List Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (collector address : Nat)
    (addresses : List Nat) (candidate : Window) (windows : List Window)
    (getCandidates : env "candidates" = some (.ref collector))
    (found : heap[collector]? = some (.list (refs (address :: addresses))))
    (rows : Rows heap items collector (address :: addresses) (candidate :: windows)) :
    ∃ result chosen, Evaluates program env maximumExpression heap (.ref result) heap ∧
      heap[result]? = some (.tuple (pairValues items chosen)) ∧
      (candidate :: windows).argmax Window.length = some chosen := by
  obtain ⟨head, tail⟩ := List.forall₂_cons.mp rows
  obtain ⟨result, rest, finalFound⟩ := maximum_loop items heap env collector (address :: addresses) 1 addresses windows found rfl
    tail address candidate head.2
  refine ⟨result, windows.foldl (ProjectEulerStatements.ArgMaximum.select Window.length) candidate, ?_, finalFound, ?_⟩
  · apply Evaluates.extremum_sequence (items := refs (address :: addresses)) (Evaluates.lookup getCandidates)
      (by simp [Mutable.sequence, found])
    apply ExtremumReturns.next (candidate := .ref address) (score := number candidate.length)
      (afterKey := heap) (afterSelection := heap)
    · simp [extremumItem, Mutable.sequence, found, refs]
    · exact key_result items candidate heap _ address rfl head.2
    · rfl
    · exact rest
  · exact ProjectEulerStatements.ArgMaximum.argmax_cons Window.length candidate windows

def selectedValue (items : List Nat) (windows : List Window) : Nat :=
  ((windows.argmax Window.length).map (fun candidate => window items candidate.first candidate.length)).getD 0

/-- Python's keyed maximum retains the first longest candidate and reads its stored sum. -/
theorem selection_result (items : List Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (collector : Nat)
    (addresses : List Nat) (windows : List Window) (getCandidates : env "candidates" = some (.ref collector))
    (found : heap[collector]? = some (.list (refs addresses))) (rows : Rows heap items collector addresses windows) :
    Evaluates program env selectionExpression heap (number (selectedValue items windows)) heap := by
  cases rows with
  | nil =>
      apply Evaluates.conditional (flag := false) (Evaluates.lookup getCandidates)
        (by simp [Mutable.truth, found, refs])
      exact Evaluates.constant
  | @cons address candidate addresses windows head tail =>
      obtain ⟨result, chosen, evaluated, chosenFound, selected⟩ := maximum_result items heap env collector address addresses candidate windows
        getCandidates found (.cons head tail)
      simp only [selectedValue, selected, Option.map_some, Option.getD_some]
      apply Evaluates.conditional (flag := true) (Evaluates.lookup getCandidates)
        (by simp [Mutable.truth, found, refs])
      apply Evaluates.subscript (middle := heap) (afterIndex := heap)
        (by intros; intro impossible; cases impossible) evaluated Evaluates.constant
      simp [Mutable.getItem, chosenFound, pairValues, Mutable.index, Except.map]

private def inputBase (heap : Mutable.Heap) (limit : Int) : Mutable.Heap :=
  heap ++ [.list (numbers (integers (primes_below.values limit.toNat))),
    .list (numbers (prefix_sums.values (integers (primes_below.values limit.toNat))))]

private def initialLocals (env : HeapCalls.Env) (heap : Mutable.Heap) : HeapCalls.Env :=
  setLocal (setLocal (setLocal env "ps" (.ref heap.length)) "pref" (.ref (heap.length + 1))) "candidates" (.ref (heap.length + 2))

private theorem setup (limit : Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (getLimit : env "limit" = some (number limit)) :
    BlockContinues program env (code.take 3) heap (initialLocals env heap) (inputBase heap limit ++ [.list []]) := by
  let psHeap := heap ++ [.list (numbers (integers (primes_below.values limit.toNat)))]
  let firstEnv := setLocal env "ps" (.ref heap.length)
  let secondEnv := setLocal firstEnv "pref" (.ref (heap.length + 1))
  have first : BlockContinues program env [code[0]'(by decide)] heap firstEnv psHeap := by
    apply BlockContinues.assign
    exact Evaluates.call (values := [number limit]) (.cons (Evaluates.lookup getLimit) .nil) (primes_below.result limit heap)
  have second : BlockContinues program firstEnv [code[1]'(by decide)] psHeap secondEnv (inputBase heap limit) := by
    apply BlockContinues.assign
    apply Evaluates.call (values := [.ref heap.length]) (.cons (Evaluates.lookup (by simp [firstEnv, setLocal])) .nil)
    have executed := prefix_sums.result (integers (primes_below.values limit.toNat)) psHeap heap.length (by simp [psHeap])
    simpa only [psHeap, inputBase, List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      List.append_assoc, List.cons_append, List.nil_append] using executed
  have third : BlockContinues program secondEnv [code[2]'(by decide)] (inputBase heap limit) (initialLocals env heap)
      (inputBase heap limit ++ [.list []]) := by
    apply BlockContinues.assign
    simpa [inputBase] using (Evaluates.list (module := program) (env := secondEnv) (heap := inputBase heap limit) Evaluates.Arguments.nil)
  exact first.append (second.append third)

def answer (limit : Int) : Nat :=
  selectedValue (primes_below.values limit.toNat) (candidates (primes_below.values limit.toNat) limit.toNat)

/-- The complete exhaustive reference terminates at every signed limit and preserves the incoming heap. -/
theorem result (limit : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap (number (answer limit)) (heap ++ extra) := by
  let env := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let base := inputBase heap limit
  let ready := initialLocals env heap
  have inputs : Inputs base (primes_below.values limit.toNat) heap.length (heap.length + 1) := by
    constructor <;> simp [base, inputBase]
  have locals : Locals ready limit base.length heap.length (heap.length + 1) := by
    constructor <;> simp [ready, initialLocals, base, inputBase, setLocal]
    rfl
  obtain ⟨finalEnv, addresses, garbage, enumerated, rows, finalLocals⟩ :=
    enumerate (primes_below.values limit.toNat) limit heap.length (heap.length + 1) base ready inputs locals
  let finalHeap := working base (refs addresses) garbage
  have selected := selection_result (primes_below.values limit.toNat) finalHeap finalEnv base.length addresses
    (candidates (primes_below.values limit.toNat) limit.toNat) finalLocals.getCandidates (by simp [finalHeap, found]) rows
  have finished : BlockReturns program finalEnv (code.drop 4) finalHeap (number (answer limit)) finalHeap :=
    BlockReturns.return_value selected
  refine ⟨[.list (numbers (integers (primes_below.values limit.toNat))),
    .list (numbers (prefix_sums.values (integers (primes_below.values limit.toNat)))), .list (refs addresses)] ++ garbage, ?_⟩
  apply BlockReturns.function rfl rfl
  have returned : BlockReturns program env (code.take 4 ++ code.drop 4) heap (number (answer limit)) finalHeap :=
    ((setup limit heap env rfl).append enumerated).returns finished
  simpa only [List.take_append_drop, finalHeap, working, base, inputBase, List.append_assoc, List.cons_append, List.nil_append] using returned

theorem «Returns» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  obtain ⟨extra, returned⟩ := result limit []
  exact returned.scalar_returns

theorem «Supported» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported := («Returns» limit).supported

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p50
