import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p43.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.HeapWindows
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.PermutationSums
import ProjectEulerSolutions.Lib.SubstringDivisibility
import lang.py.FormalSW.ScalarSetLemmas
import lang.py.FormalSW.SetCalls

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p43
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.SubstringDivisibility
private abbrev program := P43Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def numbers (items : List Nat) := items.map number
private def keys (items : List Nat) := items.map (fun (n : Nat) => Constant.int n)
variable {globals : Mutable.Globals}

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["sub_num", "has_property", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem convert_list (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue (globals := globals) program "of_digits_be" [.ref address] heap
      (number (value items)) (heap ++ [.list (numbers items.reverse)]) := by
  have converted := (common.of_digits_be.result (items.map (fun n : Nat => (n : Int))) 10
    heap address (by simpa [numbers, List.map_map] using found) globals).extend common_extension
  have defaulted := ReturnsValue.with_defaults (name := "of_digits_be")
    (supplied := [.ref address]) rfl rfl rfl converted
  have interpreted : ProjectEulerStatements.PositionalDigits.value 10
      (items.map (fun n : Nat => (n : Int))).reverse = (value items : Int) := by
    rw [← List.map_reverse]
    exact ProjectEulerStatements.PositionalDigits.value_naturals 10 items.reverse
  simpa only [interpreted, numbers, List.map_map, Function.comp_def, List.map_reverse] using defaulted

namespace sub_num
def window (items : List Nat) (start : Nat) : List Nat := (items.drop start).take 3
def garbage (items : List Nat) (start : Nat) : Mutable.Heap :=
  [.list (numbers (window items start)), .list (numbers (window items start).reverse)]

theorem result (items : List Nat) (size : items.length = 10) (start : Nat) (bound : start ≤ 7)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue (globals := globals) program "sub_num" [.ref address, number start] heap
      (number (value (window items start))) (heap ++ garbage items start) := by
  let env := functionEnv ((findFunctionIn program.body "sub_num").getD ([], [])).1
    ((findFunctionIn program.body "sub_num").getD ([], [])).2 [.ref address, number start] globals
  have sliced : Evaluates (globals := globals) program env
      (.subscript (.name "ds") (.slice (some (.name "i"))
        (some (.binOp (.name "i") .add (.constant (.int 3)))) none))
      heap (.ref heap.length) (heap ++ [.list (numbers (window items start))]) := by
    apply Evaluates.slice (receiver := .ref address) (first := number start)
      (last := .scalar (.int ((start : Int)+3))) (stepValue := .scalar .none)
      (.cons (Evaluates.lookup (by cases globals <;> rfl))
        (.cons (Evaluates.lookup (by cases globals <;> rfl))
          (.cons (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
            (av := number start) (bv := number 3)
            (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant rfl)
            (.cons Evaluates.constant .nil))))
    simpa only [numbers, window, List.map_drop, List.map_take] using
      ProjectEulerSolutions.HeapWindows.getSlice_three heap address (numbers items) found
        (by simpa [numbers] using size) start bound
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have converted := convert_list (globals := globals) (window items start)
    (heap ++ [.list (numbers (window items start))]) heap.length (by simp)
  simpa only [garbage, List.append_assoc, List.singleton_append] using
    Evaluates.call (.cons sliced .nil) converted
end sub_num

def checks : List (Nat × Nat) := [(1,2),(2,3),(3,5),(4,7),(5,11),(6,13),(7,17)]
def checkValue (items : List Nat) (pair : Nat × Nat) : Bool :=
  decide (value (sub_num.window items pair.1) % pair.2 = 0)
def property (items : List Nat) : Bool := checks.all (checkValue items)

namespace has_property
private def checkExpression (pair : Nat × Nat) : Expr :=
  .compare (.binOp (.call (.name "sub_num") [.name "ds", .constant (.int pair.1)])
    .mod (.constant (.int pair.2))) [(.eq, .constant (.int 0))]

private theorem check_result (items : List Nat) (size : items.length = 10)
    (pair : Nat × Nat) (bound : pair.1 ≤ 7) (positive : 0 < pair.2)
    (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getDs : env "ds" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    Evaluates (globals := globals) program env (checkExpression pair) heap
      (flag (checkValue items pair)) (heap ++ sub_num.garbage items pair.1) := by
  let finalHeap := heap ++ sub_num.garbage items pair.1
  apply Evaluates.compare (middle := finalHeap) (afterRight := finalHeap)
    (av := number (value (sub_num.window items pair.1) % pair.2)) (bv := number 0)
  · apply Evaluates.binary (middle := finalHeap) (afterRight := finalHeap) (finalHeap := finalHeap)
      (av := number (value (sub_num.window items pair.1))) (bv := number pair.2)
    · exact Evaluates.call (.cons (Evaluates.lookup getDs) (.cons Evaluates.constant .nil))
        (sub_num.result items size pair.1 bound heap address found)
    · exact Evaluates.constant
    · simp [Mutable.binary, scalarBinary, number, positive, positive.ne']
  · exact Evaluates.constant
  · change some (Except.ok (ε := ExceptionObject)
      (flag (decide (((value (sub_num.window items pair.1) % pair.2 : Nat) : Int) = 0))), finalHeap) = _
    simp only [Int.natCast_eq_zero, checkValue, finalHeap]

private theorem checks_result (items : List Nat) (size : items.length = 10)
    (tests : List (Nat × Nat)) (nonempty : tests ≠ [])
    (bounds : ∀ pair ∈ tests, pair.1 ≤ 7 ∧ 0 < pair.2)
    (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getDs : env "ds" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    ∃ extra, Evaluates (globals := globals) program env (.boolOp .and (tests.map checkExpression)) heap
      (flag (tests.all (checkValue items))) (heap ++ extra) := by
  induction tests generalizing heap with
  | nil => exact (nonempty rfl).elim
  | cons first rest ih =>
      obtain ⟨bound, positive⟩ := bounds first List.mem_cons_self
      have firstResult := check_result (globals := globals) items size first bound positive heap address env getDs found
      cases rest with
      | nil =>
          refine ⟨sub_num.garbage items first.1, ?_⟩
          simpa only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true] using
            Evaluates.boolean_last (op := .and) firstResult rfl
      | cons second rest =>
          cases accepted : checkValue items first with
          | false =>
              refine ⟨sub_num.garbage items first.1, ?_⟩
              simp only [List.map_cons, List.all_cons, accepted, Bool.false_and]
              exact Evaluates.boolean_stop (flag := false) (by simpa only [accepted] using firstResult) rfl rfl
          | true =>
              obtain ⟨extra, following⟩ := ih (by simp)
                (fun pair member => bounds pair (List.mem_cons_of_mem _ member))
                (heap ++ sub_num.garbage items first.1)
                (ProjectEulerSolutions.HeapCollection.prefix_found heap _ address _ found)
              refine ⟨sub_num.garbage items first.1 ++ extra, ?_⟩
              simp only [List.map_cons, List.all_cons, accepted, Bool.true_and]
              apply Evaluates.boolean_next (flag := true) (by simpa only [accepted] using firstResult) rfl rfl
              simpa only [List.append_assoc, List.map_cons] using following

private theorem eraseDups_eq (items : List Nat) (distinct : items.Nodup) : items.eraseDups = items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
      have filtered : rest.filter (fun n => !(n == first)) = rest := by
        apply List.filter_eq_self.mpr
        intro n member
        have different : n ≠ first := by intro equal; subst n; exact fresh member
        simp [different]
      simp only [List.eraseDups_cons, filtered, ih tailDistinct]

theorem result (items : List Nat) (size : items.length = 10) (distinct : items.Nodup)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (numbers items))) :
    ∃ extra, ReturnsValue (globals := globals) program "has_property" [.ref address] heap
      (flag (property items)) (heap ++ extra) := by
  let env := functionEnv ((findFunctionIn program.body "has_property").getD ([], [])).1
    ((findFunctionIn program.body "has_property").getD ([], [])).2 [.ref address] globals
  have getDs : env "ds" = some (.ref address) := by cases globals <;> rfl
  have lengthResult : Evaluates (globals := globals) program env
      (.compare (.builtinCall .len [.name "ds"]) [(.eq, .constant (.int 10))]) heap (flag true) heap := by
    apply Evaluates.compare (middle := heap) (afterRight := heap) (av := number 10) (bv := number 10)
      (Evaluates.builtin (.cons (Evaluates.lookup getDs) .nil)
        (by simp [primitive, Mutable.length, found, numbers, size])) Evaluates.constant rfl
  let setHeap := heap ++ [.set (keys items)]
  have setResult : Evaluates (globals := globals) program env (.builtinCall .set [.name "ds"])
      heap (.ref heap.length) setHeap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getDs) .nil)
    have allocated := Mutable.setFrom_list heap address (keys items)
      (by simpa [keys, numbers, List.map_map] using found)
    have built := ScalarSet.fold_insert_nats items
    simpa only [primitive, keys, built, eraseDups_eq items distinct] using allocated
  have distinctResult : Evaluates (globals := globals) program env
      (.compare (.builtinCall .len [.builtinCall .set [.name "ds"]]) [(.eq, .constant (.int 10))])
      heap (flag true) setHeap := by
    apply Evaluates.compare (middle := setHeap) (afterRight := setHeap) (av := number 10) (bv := number 10)
      (Evaluates.builtin (.cons setResult .nil)
        (by simp [primitive, Mutable.length, setHeap, keys, size])) Evaluates.constant rfl
  obtain ⟨extra, tested⟩ := checks_result (globals := globals) items size checks (by decide)
    (by intro pair member; revert pair; decide +kernel) setHeap address env getDs
    (ProjectEulerSolutions.HeapCollection.prefix_found heap _ address _ found)
  refine ⟨[.set (keys items)] ++ extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.boolean_next (flag := true) lengthResult rfl rfl
  apply Evaluates.boolean_next (flag := true) distinctResult rfl rfl
  simpa only [checkExpression, checks, List.map_cons, List.map_nil, property,
    setHeap, List.append_assoc] using tested
end has_property


/-- On a complete permutation the source's seven checks are exactly the mathematical tests. -/
theorem property_eq_accepts (items : List Nat) (size : items.length = 10) :
    property items = ProjectEulerSolutions.ConstraintRows.accepts tests items := by
  obtain ⟨a, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨b, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨c, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨d, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨e, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨f, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨g, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨h, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨i, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  obtain ⟨j, items, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < items.length)
  simp only [List.length_cons] at size
  have empty : items = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst items
  have three (x y z : Nat) : value [x,y,z] = triple x y z := by
    simp [value, Nat.ofDigits, triple]
    omega
  rw [accepts_digits]
  simp [property, checks, checkValue, sub_num.window, three]

namespace naive
private def sources (items : List Nat) : List SequenceSource :=
  items.map (fun (n : Nat) => .scalar (.int n))
private abbrev predicate : Expr := .call (.name "has_property") [.builtinCall .list [.name "p"]]
private abbrev conversion : Expr := .call (.name "of_digits_be") [.builtinCall .list [.name "p"]]
private def body : List Stmt := [.ifThen predicate (sumBody conversion []) []]
private def fold (rows : List (List Nat)) (initial : Nat) : Nat :=
  rows.foldl (fun total row => if property row then total + value row else total) initial

private theorem fold_sum (rows : List (List Nat)) (initial : Nat) :
    fold rows initial = initial + ((rows.filter property).map value).sum := by
  induction rows generalizing initial with
  | nil => simp [fold]
  | cons row rows ih =>
      change fold rows (if property row then initial+value row else initial) = _
      rw [ih]
      cases accepted : property row <;> simp [accepted, Nat.add_assoc]

private theorem tuple_predicate (items : List Nat) (size : items.length = 10) (distinct : items.Nodup)
    (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getP : env "p" = some (.ref address)) (found : heap[address]? = some (.tuple (numbers items))) :
    ∃ extra, Evaluates (globals := globals) program env predicate heap
      (flag (property items)) (heap ++ extra) := by
  have copied : Evaluates (globals := globals) program env (.builtinCall .list [.name "p"])
      heap (.ref heap.length) (heap ++ [.list (numbers items)]) :=
    Evaluates.builtin (.cons (Evaluates.lookup getP) .nil) (primitive_list_tuple heap address _ found)
  obtain ⟨extra, tested⟩ := has_property.result (globals := globals) items size distinct
    (heap ++ [.list (numbers items)]) heap.length (by simp)
  refine ⟨[.list (numbers items)] ++ extra, ?_⟩
  simpa only [List.append_assoc] using Evaluates.call (.cons copied .nil) tested

private theorem tuple_value (items : List Nat) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getP : env "p" = some (.ref address)) (found : heap[address]? = some (.tuple (numbers items))) :
    Evaluates (globals := globals) program env conversion heap (number (value items))
      (heap ++ [.list (numbers items), .list (numbers items.reverse)]) := by
  have copied : Evaluates (globals := globals) program env (.builtinCall .list [.name "p"])
      heap (.ref heap.length) (heap ++ [.list (numbers items)]) :=
    Evaluates.builtin (.cons (Evaluates.lookup getP) .nil) (primitive_list_tuple heap address _ found)
  have converted := convert_list (globals := globals) items (heap ++ [.list (numbers items)]) heap.length (by simp)
  simpa only [List.append_assoc, List.singleton_append] using Evaluates.call (.cons copied .nil) converted

private theorem sum_rows (remaining : List (List Nat))
    (valid : ∀ row ∈ remaining, row.Perm pool) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (initial : Nat) (accumulator : env sumAccumulator = some (number initial)) :
    ∃ extra, BlockReturns (globals := globals) program env
      [.permutationStepLoop "p" (remaining.map sources) body [], .return (.name sumAccumulator)]
      heap (number (fold remaining initial)) (heap ++ extra) := by
  induction remaining generalizing heap env initial with
  | nil =>
      refine ⟨[], ?_⟩
      simpa only [List.map_nil, fold, List.foldl_nil, List.append_nil] using
        BlockReturns.permutation_done (BlockReturns.return_value (Evaluates.lookup accumulator))
  | cons row remaining ih =>
      have permuted := valid row List.mem_cons_self
      have size : row.length = 10 := by simpa [pool] using permuted.length_eq
      have distinct := permuted.nodup_iff.mpr pool_nodup
      obtain ⟨address, tupleExtra, allocated, tuple⟩ :=
        ProjectEulerSolutions.HeapCollection.allocate_tuple (numbers row) heap
      let tupleHeap := heap ++ tupleExtra
      let bound := setLocal env "p" (.ref address)
      have saved : bound sumAccumulator = some (number initial) := by
        simpa [bound, setLocal, sumAccumulator] using accumulator
      obtain ⟨testExtra, tested⟩ := tuple_predicate (globals := globals) row size distinct
        tupleHeap address bound (by simp [bound, setLocal]) tuple
      have validTail : ∀ row ∈ remaining, row.Perm pool :=
        fun row member => valid row (List.mem_cons_of_mem _ member)
      cases accepted : property row with
      | false =>
          obtain ⟨extra, rest⟩ := ih validTail (tupleHeap ++ testExtra) bound initial saved
          refine ⟨tupleExtra ++ testExtra ++ extra, ?_⟩
          simp only [List.map_cons, fold, List.foldl_cons, accepted, Bool.false_eq_true, if_false]
          apply BlockReturns.permutation_step (tuple := .ref address) (middle := tupleHeap)
            (by simpa [sources, numbers, List.map_map, Function.comp_def] using allocated)
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using tested) rfl
          simpa only [body, sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, tupleHeap, List.append_assoc, fold] using rest
      | true =>
          let valueExtra : Mutable.Heap := [.list (numbers row), .list (numbers row.reverse)]
          have converted := tuple_value (globals := globals) row (tupleHeap ++ testExtra) address bound
            (by simp [bound, setLocal])
            (ProjectEulerSolutions.HeapCollection.prefix_found tupleHeap testExtra address _ tuple)
          let following := setLocal bound sumAccumulator (number (initial+value row))
          obtain ⟨extra, rest⟩ := ih validTail ((tupleHeap ++ testExtra) ++ valueExtra)
            following (initial+value row) (by simp [following, setLocal])
          refine ⟨tupleExtra ++ testExtra ++ valueExtra ++ extra, ?_⟩
          simp only [List.map_cons, fold, List.foldl_cons, accepted, if_true]
          apply BlockReturns.permutation_step (tuple := .ref address) (middle := tupleHeap)
            (by simpa [sources, numbers, List.map_map, Function.comp_def] using allocated)
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using tested) rfl
          apply BlockReturns.assign (middle := (tupleHeap ++ testExtra) ++ valueExtra)
            (value := number (initial+value row))
          · exact Evaluates.binary (Evaluates.lookup saved) converted
              (by simp [Mutable.binary, scalarBinary, number, valueExtra])
          · simpa only [body, sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
              Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, tupleHeap, List.append_assoc,
              fold, following] using rest
private def allRows : List (List Nat) := Permutations.rows 10 pool

private theorem valid_rows (row : List Nat) (member : row ∈ allRows) : row.Perm pool :=
  Permutations.row_perm 10 pool row (by decide) member

private theorem final_sum : fold allRows 0 = (referenceRows.map value).sum := by
  have filtered : allRows.filter property = referenceRows := by
    change (Permutations.rows 10 pool).filter property =
      (Permutations.rows 10 pool).filter (ProjectEulerSolutions.ConstraintRows.accepts tests)
    apply List.filter_congr
    intro row member
    exact property_eq_accepts row (by simpa [pool] using (valid_rows row member).length_eq)
  rw [fold_sum, Nat.zero_add, filtered]

/-- The complete reference sum terminates, preserves the original heap, and returns the mathematical sum. -/
theorem result (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "naive" [] heap
      (number (referenceRows.map value).sum) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [] globals
  obtain ⟨poolExtra, mapped⟩ := ProjectEulerSolutions.HeapCollection.range_map
    (globals := globals) program "d" (.name "d") number
    (fun heap env n getD => ⟨[], by simpa using
      (Evaluates.lookup (globals := globals) (module := program) (heap := heap) getD)⟩)
    heap initial [.constant (.int 10)] [number 10] 0 10 (.cons Evaluates.constant .nil) rfl
  let afterPool := ProjectEulerSolutions.HeapCollection.working heap (numbers pool) poolExtra
  let ready := setLocal initial "digits" (.ref heap.length)
  let inner := setLocal
    (comprehensionTargetsEnv ready [(.name "p", .permutationsIterable [.name "digits", .constant .none], [predicate])])
    sumAccumulator (number 0)
  have collected : Evaluates (globals := globals) program initial
      (.listComp (.name "d") [("d", .call (.name "range") [.constant (.int 10)], [])])
      heap (.ref heap.length) afterPool := by
    simpa only [afterPool, numbers, pool, List.range_eq_range'] using mapped
  have captured : permutationRows [.ref heap.length, .scalar .none] afterPool =
      some (.ok (allRows.map sources), afterPool) := by
    have found := ProjectEulerSolutions.HeapCollection.found heap (numbers pool) poolExtra
    have acquired := permutationRows_list afterPool heap.length (numbers pool) found
    simpa only [numbers, List.length_map, show pool.length = 10 from rfl, Permutations.rows_map,
      List.map_map, Function.comp_def, allRows, sources, sequenceSource] using acquired
  obtain ⟨extra, executed⟩ := sum_rows (globals := globals) allRows valid_rows afterPool inner 0
    (by simp [inner, setLocal])
  have summed : Evaluates (globals := globals) program ready
      (.sumGeneratorTargets conversion
        [(.name "p", .permutationsIterable [.name "digits", .constant .none], [predicate])]
        (.constant (.int 0))) afterPool (number (referenceRows.map value).sum) (afterPool ++ extra) := by
    apply ProjectEulerSolutions.PermutationSums.evaluate
      (.cons (Evaluates.lookup (by simp [ready, setLocal])) (.cons Evaluates.constant .nil))
      captured Evaluates.constant rfl
    simpa only [final_sum] using executed
  refine ⟨(.list (numbers pool) :: poolExtra) ++ extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign collected
  apply BlockReturns.return_value
  simpa only [afterPool, ProjectEulerSolutions.HeapCollection.working, List.append_assoc] using summed

theorem «Returns» : (SetCalls.call program "naive" [] []).Returns := by
  obtain ⟨extra, returned⟩ := result (globals := []) []
  intro choices
  exact SetCalls.returns_of_heap returned.returns choices

theorem «Supported» : (SetCalls.call program "naive" [] []).Supported := by
  intro choices
  exact («Returns» choices).supported
end naive

end data.«project-euler-statements».data.py.project_euler_statements.p43
