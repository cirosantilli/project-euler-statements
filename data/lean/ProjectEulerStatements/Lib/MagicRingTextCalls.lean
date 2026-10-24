import ProjectEulerStatements.Lib.MagicRingIndexing
import lang.py.FormalSW.HeapCalls

/-! Shared source execution of the two identical ring-string helpers. -/
namespace ProjectEulerStatements.MagicRingTextCalls
open FormalSW.PyAst HeapCalls MagicRing
set_option Elab.async false

abbrev number (value : Nat) : Mutable.Value := .scalar (.int value)
abbrev string (value : String) : Mutable.Value := .scalar (.string value)
def encode (values : List Nat) : List Mutable.Value := values.map number
def encodedStrings (values : List String) : List Mutable.Value := values.map string
def working (base : Mutable.Heap) (parts : List String) : Mutable.Heap :=
  base ++ [.list (encodedStrings parts)]
def pieces {n : Nat} (ring : Ring n) (start count : Nat) : List String :=
  (List.range count).map (fun offset => lineText ring.outer ring.inner ((start + offset) % n))

theorem pieces_succ {n : Nat} (ring : Ring n) (start count : Nat) :
    pieces ring start (count + 1) = pieces ring start count ++
      [lineText ring.outer ring.inner ((start + count) % n)] := by
  simp [pieces, List.range_succ]

theorem pieces_text {n : Nat} (ring : Ring n) (start : Nat) :
    String.join (pieces ring start n) = textFrom ring.outer ring.inner start := by
  simp only [pieces, textFrom, ring.inner_length]

theorem found (base : Mutable.Heap) (parts : List String) :
    (working base parts)[base.length]? = some (.list (encodedStrings parts)) := by simp [working]

theorem prefix_found (base : Mutable.Heap) (parts : List String) (address : Nat)
    (object : Mutable.Object)
    (read : base[address]? = some object) : (working base parts)[address]? = some object := by
  unfold working
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
  exact read

def object (tuple : Bool) (items : List Nat) : Mutable.Object :=
  if tuple then .tuple (encode items) else .list (encode items)

theorem index_evaluates (program : Module) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (name : String) (address index : Nat) (tuple : Bool) (items : List Nat)
    (value : Nat) (key : Expr)
    (receiver : env name = some (.ref address))
    (evaluated : Evaluates program env key heap (number index) heap)
    (ordinary : ∀ a b c, key ≠ .slice a b c)
    (contents : heap[address]? = some (object tuple items))
    (read : items[index]? = some value) :
    Evaluates program env (.subscript (.name name) key) heap (number value) heap := by
  have inside : index < items.length := (List.getElem?_eq_some_iff.mp read).1
  apply Evaluates.subscript ordinary (Evaluates.lookup receiver) evaluated
  cases tuple <;> simp [object] at contents <;>
    simp [Mutable.getItem, contents, Mutable.index, encode, number, read,
      show ¬ (index : Int) < 0 by omega, show ¬ items.length ≤ index by omega, Except.map]

def element : Expr :=
  .binOp (.binOp (.builtinCall .str [.subscript (.name "outer") (.name "index")]) .add
    (.builtinCall .str [.subscript (.name "inner") (.name "index")])) .add
    (.builtinCall .str [.subscript (.name "inner")
      (.binOp (.binOp (.name "index") .add (.constant (.int 1))) .mod (.name "n"))])
def body : List Stmt :=
  [.assign [.name "index"]
     (.binOp (.binOp (.name "start") .add (.name "offset")) .mod (.name "n")),
   .expr (.call (.attribute (.name "parts") "append") [element])]
def code : List Stmt :=
  [.assign [.name "n"] (.builtinCall .len [.name "inner"]),
   .annAssign (.name "parts") (.subscript (.name "list") (.name "str")) (some (.list [])),
   .forIn (.name "offset") (.call (.name "range") [.name "n"]) body [],
   .return (.call (.attribute (.constant (.string "")) "join") [.name "parts"])]

structure Ready (n start outerAddress innerAddress partsAddress : Nat)
    (env : HeapCalls.Env) : Prop where
  getN : env "n" = some (number n)
  getStart : env "start" = some (number start)
  getOuter : env "outer" = some (.ref outerAddress)
  getInner : env "inner" = some (.ref innerAddress)
  getParts : env "parts" = some (.ref partsAddress)

theorem element_result (program : Module) {n : Nat} (ring : Ring n)
    (index : Nat) (inside : index < n)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (localOuter : env "outer" = some (.ref outerAddress))
    (localInner : env "inner" = some (.ref innerAddress))
    (localIndex : env "index" = some (number index)) (localN : env "n" = some (number n)) :
    Evaluates program env element heap (string (lineText ring.outer ring.inner index)) heap := by
  have outerInside : index < ring.outer.length := by rw [ring.outer_length]; exact inside
  have innerInside : index < ring.inner.length := by rw [ring.inner_length]; exact inside
  have nextInside : (index + 1) % n < ring.inner.length := by
    rw [ring.inner_length]
    exact Nat.mod_lt _ (by omega)
  have nextIndex : Evaluates program env
      (.binOp (.binOp (.name "index") .add (.constant (.int 1))) .mod (.name "n")) heap
      (number ((index + 1) % n)) heap := by
    exact Evaluates.binary (av := number (index + 1)) (bv := number n) (middle := heap)
      (afterRight := heap)
      (Evaluates.binary (Evaluates.lookup localIndex) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) (Evaluates.lookup localN)
      (by simp [Mutable.binary, scalarBinary, number,
        show 0 < n by omega, show n ≠ 0 by omega])
  have outerRead := index_evaluates program heap env "outer" outerAddress index false ring.outer
    ((ring.outer[index]?).getD 0) (.name "index") localOuter (Evaluates.lookup localIndex)
    (by intros a b c impossible; cases impossible) getOuter
    (by rw [List.getElem?_eq_getElem outerInside]; rfl)
  have innerRead := index_evaluates program heap env "inner" innerAddress index true ring.inner
    ((ring.inner[index]?).getD 0) (.name "index") localInner (Evaluates.lookup localIndex)
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem innerInside]; rfl)
  have nextRead := index_evaluates program heap env "inner" innerAddress
    ((index + 1) % n) true ring.inner
    ((ring.inner[(index + 1) % n]?).getD 0) _ localInner nextIndex
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem nextInside]; rfl)
  apply Evaluates.binary (middle := heap) (afterRight := heap)
    (av := string (toString (((ring.outer[index]?).getD 0 : Nat) : Int) ++
      toString (((ring.inner[index]?).getD 0 : Nat) : Int)))
    (bv := string (toString (((ring.inner[(index + 1) % n]?).getD 0 : Nat) : Int)))
  · exact Evaluates.binary (middle := heap) (afterRight := heap)
      (Evaluates.builtin (.cons outerRead .nil) rfl)
      (Evaluates.builtin (.cons innerRead .nil) rfl) rfl
  · exact Evaluates.builtin (.cons nextRead .nil) rfl
  · simp only [lineText, ring.inner_length]
    rfl

theorem intercalate_empty (parts : List String) : "".intercalate parts = String.join parts := by
  induction parts with
  | nil => rfl
  | cons first rest ih => cases rest <;> simp_all

theorem loop_result (program : Module) {n : Nat} (ring : Ring n) (start count : Nat)
    (before : count ≤ n) (base : Mutable.Heap) (env : HeapCalls.Env)
    (outerAddress innerAddress : Nat)
    (getOuter : base[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : base[innerAddress]? = some (.tuple (encode ring.inner)))
    (ready : Ready n start outerAddress innerAddress base.length env) :
    BlockReturns program env
      [.rangeStepLoop "offset" count n 1 body [], code[3]'(by decide)]
      (working base (pieces ring start count)) (string (textFrom ring.outer ring.inner start))
      (working base (pieces ring start n)) := by
  by_cases active : count < n
  · let index := (start + count) % n
    let indexed := setLocal env "offset" (number count)
    let nextEnv := setLocal indexed "index" (number index)
    let heap := working base (pieces ring start count)
    have inside : index < n := Nat.mod_lt _ (by omega)
    have position : Evaluates program indexed
        (.binOp (.binOp (.name "start") .add (.name "offset")) .mod (.name "n")) heap
        (number index) heap := by
      exact Evaluates.binary (av := number (start + count)) (bv := number n) (middle := heap)
        (afterRight := heap)
        (Evaluates.binary (Evaluates.lookup (by simpa [indexed, setLocal] using ready.getStart))
          (Evaluates.lookup rfl) (by simp [Mutable.binary, scalarBinary, number]))
        (Evaluates.lookup (by simpa [indexed, setLocal] using ready.getN))
        (by simp [Mutable.binary, scalarBinary, number, index,
          show 0 < n by omega, show n ≠ 0 by omega])
    have item := element_result program ring index inside heap nextEnv outerAddress innerAddress
      (prefix_found base _ outerAddress _ getOuter) (prefix_found base _ innerAddress _ getInner)
      (by simpa [nextEnv, indexed, setLocal] using ready.getOuter)
      (by simpa [nextEnv, indexed, setLocal] using ready.getInner) rfl
      (by simpa [nextEnv, indexed, setLocal] using ready.getN)
    have appended := Evaluates.append (base := .name "parts")
      (Evaluates.lookup (by simpa [nextEnv, indexed, setLocal] using ready.getParts))
      (found base _) item (found base _)
    have wrote : Evaluates program nextEnv (.call (.attribute (.name "parts") "append") [element])
        heap (.scalar .none) (working base (pieces ring start (count + 1))) := by
      simpa [heap, working, pieces_succ, encodedStrings, string, index, List.map_append,
        List.set_append_right] using appended
    apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
    apply BlockReturns.assign position
    apply BlockReturns.discard wrote
    have nextReady : Ready n start outerAddress innerAddress base.length nextEnv := by
      constructor
      · simpa [nextEnv, indexed, setLocal] using ready.getN
      · simpa [nextEnv, indexed, setLocal] using ready.getStart
      · simpa [nextEnv, indexed, setLocal] using ready.getOuter
      · simpa [nextEnv, indexed, setLocal] using ready.getInner
      · simpa [nextEnv, indexed, setLocal] using ready.getParts
    have rest := loop_result program ring start (count + 1) (by omega) base nextEnv
      outerAddress innerAddress getOuter getInner nextReady
    simpa only [Calls.loopContinuation, show Calls.loopControl body = false from rfl,
      Bool.false_eq_true, if_false] using rest
  · have same : count = n := by omega
    subst count
    apply BlockReturns.range_done (by simp [Calls.rangeContinues])
    apply BlockReturns.return_value
    apply Evaluates.join (middle := working base (pieces ring start n)) Evaluates.constant
      (.cons (Evaluates.lookup ready.getParts) .nil)
    · have joined := primitive_join_list (working base (pieces ring start n)) base.length ""
        (pieces ring start n) (found base _)
      simpa only [intercalate_empty, pieces_text] using joined
    · intro name impossible
      cases impossible
termination_by n - count
decreasing_by omega

theorem result (program : Module) (outerArg innerArg startArg : Arg)
    (outerName : outerArg.name = "outer") (innerName : innerArg.name = "inner")
    (startName : startArg.name = "start")
    (function : findFunctionIn program.body "ring_string" =
      some ([outerArg, innerArg, startArg], code))
    {n : Nat} (ring : Ring n) (start : Nat) (base : Mutable.Heap)
    (outerAddress innerAddress : Nat)
    (getOuter : base[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : base[innerAddress]? = some (.tuple (encode ring.inner))) :
    ReturnsValue program "ring_string" [.ref outerAddress, .ref innerAddress, number start] base
      (string (textFrom ring.outer ring.inner start)) (working base (pieces ring start n)) := by
  let args := [outerArg, innerArg, startArg]
  let env := argumentEnv args [.ref outerAddress, .ref innerAddress, number start]
  let sized := setLocal env "n" (number n)
  let prepared := setLocal sized "parts" (.ref base.length)
  have localOuter : env "outer" = some (.ref outerAddress) := by
    simp [env, args, HeapCalls.argumentEnv, outerName, innerName, startName]
  have localInner : env "inner" = some (.ref innerAddress) := by
    simp [env, args, HeapCalls.argumentEnv, outerName, innerName, startName, List.lookup]
  have localStart : env "start" = some (number start) := by
    simp [env, args, HeapCalls.argumentEnv, outerName, innerName, startName, List.lookup]
  have size : Evaluates program env (.builtinCall .len [.name "inner"]) base (number n) base :=
    Evaluates.builtin (.cons (Evaluates.lookup localInner) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, getInner, encode, ring.inner_length, number])
  have allocation : Evaluates program sized (.list []) base (.ref base.length) (working base []) :=
    Evaluates.list .nil
  have ready : Ready n start outerAddress innerAddress base.length prepared := by
    constructor
    · simp [prepared, sized, setLocal]
    · simpa [prepared, sized, setLocal] using localStart
    · simpa [prepared, sized, setLocal] using localOuter
    · simpa [prepared, sized, setLocal] using localInner
    · rfl
  have loop := loop_result program ring start 0 (Nat.zero_le _) base prepared outerAddress
    innerAddress getOuter getInner ready
  apply BlockReturns.function function rfl
  apply BlockReturns.assign size
  apply (BlockContinues.annAssign allocation).returns
  apply BlockReturns.for_range (.cons (Evaluates.lookup ready.getN) .nil) rfl
  simpa only [Nat.cast_zero, pieces, List.range_zero, List.map_nil] using loop

end ProjectEulerStatements.MagicRingTextCalls
