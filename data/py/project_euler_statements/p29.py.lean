import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p29.py.ast»
import lang.py.FormalSW.HeapCalls
import ProjectEulerStatements.P29
import Mathlib.Data.List.Range
import Mathlib.Data.Int.Cast.Lemmas

namespace data.«project-euler-statements».data.py.project_euler_statements.p29
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := P29Ast.module
private abbrev num (n : Nat) : Mutable.Value := .scalar (.int n)
def numbers (values : List Nat) : List Mutable.Value := values.map num
def row (a count : Nat) : List Nat := (List.range' 2 count).map (a ^ ·)
def values (a b : Int) : List Nat :=
  (List.range' 2 (a - 1).toNat).flatMap (fun x => row x (b - 1).toNat)
def keys (values : List Nat) : List Constant := values.map (fun n : Nat => .int n)
def insertUnique (before : List Nat) (value : Nat) : List Nat :=
  if value ∈ before then before else before ++ [value]

theorem insert_keys (before : List Nat) (value : Nat) :
    ScalarSet.insert (keys before) (.int value) = keys (insertUnique before value) := by
  by_cases present : value ∈ before <;>
    simpa [keys, insertUnique, List.map_map, present] using
      ScalarSet.insert_ints (before.map (fun n : Nat => (n : Int))) value

theorem fold_keys (items before : List Nat) :
    (keys items).foldl ScalarSet.insert (keys before) = keys (items.foldl insertUnique before) := by
  induction items generalizing before with
  | nil => rfl
  | cons head tail ih =>
      change (keys tail).foldl ScalarSet.insert (ScalarSet.insert (keys before) (.int head)) =
        keys (tail.foldl insertUnique (insertUnique before head))
      rw [insert_keys]
      exact ih _

theorem fold_insert (items before : List Nat) :
    items.foldl insertUnique before.eraseDups = (before ++ items).eraseDups := by
  induction items generalizing before with
  | nil => simp
  | cons head tail ih =>
      have added : insertUnique before.eraseDups head = (before ++ [head]).eraseDups := by
        by_cases present : head ∈ before <;>
          simp [insertUnique, List.eraseDups_append, List.removeAll, List.eraseDups_cons, present]
      rw [List.foldl_cons, added, ih]
      simp

private abbrev emit (collector : Nat) : List Stmt :=
  [.comprehensionAppend collector (.binOp (.name "a") .pow (.name "b"))]

private theorem inside {heap : Mutable.Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) : address < heap.length := by
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  contradiction

private theorem set_existing {heap : Mutable.Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) : heap.set address object = heap := by
  have bound := inside found
  have equal : heap[address] = object := by simpa [List.getElem?_eq_getElem bound] using found
  rw [← equal, List.set_getElem_self]

private theorem collect_inner (count start a : Nat) (stop : Int)
    (length : (stop - start).toNat = count) (heap : Mutable.Heap) (collector : Nat)
    (before : List Nat) (env : HeapCalls.Env) (getA : env "a" = some (num a))
    (found : heap[collector]? = some (.list (numbers before))) :
    ∃ finalEnv,
      BlockContinues program env [.rangeStepLoop "b" start stop 1 (emit collector) []] heap finalEnv
        (heap.set collector (.list (numbers (before ++ (List.range' start count).map (a ^ ·))))) ∧
      finalEnv "a" = env "a" ∧ finalEnv "b_max" = env "b_max" := by
  induction count generalizing start heap before env with
  | zero =>
      have finished : stop ≤ start := by omega
      refine ⟨env, ?_, rfl, rfl⟩
      simpa only [List.range'_zero, List.map_nil, List.append_nil, set_existing found] using
        (BlockContinues.range_done (module := program) (env := env) (heap := heap)
          (name := "b") (body := emit collector) (otherwise := [])
          (next := (start : Int)) (stop := stop) (stride := 1)
          (by simp [Calls.rangeContinues]; omega) BlockContinues.nil)
  | succ count ih =>
      have continues : (start : Int) < stop := by omega
      let bound := setLocal env "b" (num start)
      let middle := heap.set collector (.list (numbers (before ++ [a ^ start])))
      have getA' : bound "a" = some (num a) := by simpa [bound, setLocal] using getA
      have emitted : BlockContinues program bound (emit collector) heap bound middle := by
        have expression : Evaluates program bound (.binOp (.name "a") .pow (.name "b"))
            heap (num (a ^ start)) heap :=
          Evaluates.binary (Evaluates.lookup getA') (Evaluates.lookup rfl)
            (by simp [Mutable.binary, scalarBinary, num, show ¬ (start : Int) < 0 by omega])
        simpa [emit, middle, numbers] using BlockContinues.comprehension_append expression found
      obtain ⟨finalEnv, rest, finalA, finalB⟩ := ih (start + 1) (by omega) middle
        (before ++ [a ^ start]) bound getA' (by apply List.getElem?_set_self; exact inside found)
      refine ⟨finalEnv, ?_, by simpa [bound, setLocal] using finalA,
        by simpa [bound, setLocal] using finalB⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues, continues])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, emit, middle,
        List.range'_succ, List.set_set, List.append_assoc, Nat.cast_add, Nat.cast_one, bound]
        using emitted.append rest

private abbrev innerBody (collector : Nat) : List Stmt :=
  [.forIn (.name "b") (.call (.name "range")
    [.constant (.int 2), .binOp (.name "b_max") .add (.constant (.int 1))]) (emit collector) []]

private theorem collect_outer (count start : Nat) (stop bMax : Int)
    (length : (stop - start).toNat = count) (heap : Mutable.Heap) (collector : Nat)
    (before : List Nat) (env : HeapCalls.Env) (getB : env "b_max" = some (.scalar (.int bMax)))
    (found : heap[collector]? = some (.list (numbers before))) :
    ∃ finalEnv,
      BlockContinues program env [.rangeStepLoop "a" start stop 1 (innerBody collector) []] heap finalEnv
        (heap.set collector (.list (numbers
          (before ++ (List.range' start count).flatMap (fun a => row a (bMax - 1).toNat))))) ∧
      finalEnv "b_max" = env "b_max" := by
  induction count generalizing start heap before env with
  | zero =>
      have finished : stop ≤ start := by omega
      refine ⟨env, ?_, rfl⟩
      simpa only [List.range'_zero, List.flatMap_nil, List.append_nil, set_existing found] using
        (BlockContinues.range_done (module := program) (env := env) (heap := heap)
          (name := "a") (body := innerBody collector) (otherwise := [])
          (next := (start : Int)) (stop := stop) (stride := 1)
          (by simp [Calls.rangeContinues]; omega) BlockContinues.nil)
  | succ count ih =>
      have continues : (start : Int) < stop := by omega
      let bound := setLocal env "a" (num start)
      let middle := heap.set collector (.list (numbers (before ++ row start (bMax - 1).toNat)))
      have getB' : bound "b_max" = some (.scalar (.int bMax)) := by simpa [bound, setLocal] using getB
      obtain ⟨nextEnv, inner, _, nextB⟩ := collect_inner (bMax - 1).toNat 2 start (bMax + 1)
        (by congr 1; omega) heap collector before bound rfl found
      have innerExecuted : BlockContinues program bound (innerBody collector) heap nextEnv middle := by
        apply BlockContinues.for_range (middle := heap) (values := [.scalar (.int 2), .scalar (.int (bMax + 1))])
        · exact .cons Evaluates.constant
            (.cons (Evaluates.binary (Evaluates.lookup getB') Evaluates.constant rfl) .nil)
        · rfl
        · exact inner
      obtain ⟨finalEnv, rest, finalB⟩ := ih (start + 1) (by omega) middle
        (before ++ row start (bMax - 1).toNat) nextEnv (nextB.trans getB')
        (by apply List.getElem?_set_self; exact inside found)
      refine ⟨finalEnv, ?_, finalB.trans (nextB.trans (by simp [bound, setLocal]))⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues, continues])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, innerBody, emit, middle,
        List.range'_succ, List.set_set, List.append_assoc, Nat.cast_add, Nat.cast_one, bound]
        using innerExecuted.append rest

theorem powers.result (a b : Int) (heap : Mutable.Heap) :
    ReturnsValue program "powers" [.scalar (.int a), .scalar (.int b)] heap
      (.ref heap.length) (heap ++ [.list (numbers (values a b))]) := by
  let env := HeapCalls.argumentEnv
    [{ name := "a_max", annotation := some (.name "int") }, { name := "b_max", annotation := some (.name "int") }]
    [.scalar (.int a), .scalar (.int b)]
  let generators : List (String × Expr × List Expr) :=
    [("a", .call (.name "range") [.constant (.int 2), .binOp (.name "a_max") .add (.constant (.int 1))], []),
     ("b", .call (.name "range") [.constant (.int 2), .binOp (.name "b_max") .add (.constant (.int 1))], [])]
  obtain ⟨finalEnv, collected, _⟩ := collect_outer (a - 1).toNat 2 (a + 1) b
    (by congr 1; omega) (heap ++ [.list []]) heap.length [] (comprehensionEnv env generators)
    rfl (by simp [numbers])
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.list_comp_range (middle := heap) (finalEnv := finalEnv)
    (values := [.scalar (.int 2), .scalar (.int (a + 1))])
  · exact .cons Evaluates.constant
      (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)
  · rfl
  · simpa [values, numbers, List.set_append, comprehensionBody, comprehensionFilters, innerBody, emit]
      using collected

theorem keys_deduplicate (items : List Nat) :
    (keys items).foldl ScalarSet.insert [] = keys items.eraseDups := by
  simpa using (fold_keys items []).trans (congrArg keys (fold_insert items []))

theorem naive.result (a b : Int) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [.scalar (.int a), .scalar (.int b)] heap
      (num (values a b).eraseDups.length)
      (heap ++ [.list (numbers (values a b)), .set (keys (values a b).eraseDups)]) := by
  let items := values a b
  let middle := heap ++ [Mutable.Object.list (numbers items)]
  have found : middle[heap.length]? = some (.list ((keys items).map Mutable.Value.scalar)) := by
    simp [middle, numbers, keys, List.map_map]
  have constructed := Mutable.setFrom_list middle heap.length (keys items) found
  rw [keys_deduplicate] at constructed
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (name := .len)
    (values := [.ref (heap.length + 1)])
    (middle := heap ++ [.list (numbers items), .set (keys items.eraseDups)])
  · apply Evaluates.Arguments.cons (middle := heap ++ [.list (numbers items), .set (keys items.eraseDups)])
    · apply Evaluates.builtin (name := .set) (values := [.ref heap.length]) (middle := middle)
      · exact .cons (Evaluates.call
          (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) (powers.result a b heap)) .nil
      · simpa [primitive, middle, List.append_assoc] using constructed
    · exact .nil
  · simp [primitive, Mutable.length, keys, num, items]

theorem values_nat (a b : Nat) : values a b = ProjectEulerStatements.P29.powers a b := by
  have aCount : ((a : Int) - 1).toNat = a - 1 := by omega
  have bCount : ((b : Int) - 1).toNat = b - 1 := by omega
  simp [values, row, aCount, bCount, ProjectEulerStatements.P29.powers,
    List.range'_eq_map_range, List.map_map, List.flatMap, Function.comp_def, Nat.add_comm]

theorem naive.«Returns» (a b : Int) :
    (HeapCalls.scalarFunction program "naive" [.int a, .int b]).Returns :=
  (naive.result a b []).scalar_returns

theorem naive.«Supported» (a b : Int) :
    (HeapCalls.scalarFunction program "naive" [.int a, .int b]).Supported :=
  (naive.«Returns» a b).supported

end data.«project-euler-statements».data.py.project_euler_statements.p29
