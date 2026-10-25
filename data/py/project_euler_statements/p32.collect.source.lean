import data.«project-euler-statements».data.py.project_euler_statements.«p32.slices.source»
import lang.py.FormalSW.SetSumCalls
import lang.py.FormalSW.ScalarSetLemmas

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions ProjectEulerSolutions.PandigitalProductSearch
private abbrev program := P32Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

def working (base : Mutable.Heap) (values : List Constant) (garbage : Mutable.Heap) : Mutable.Heap :=
  base ++ (.set values :: garbage)

@[simp] theorem working_found (base : Mutable.Heap) (values : List Constant) (garbage : Mutable.Heap) :
    (working base values garbage)[base.length]? = some (.set values) := by simp [working]

theorem working_append (base : Mutable.Heap) (values : List Constant) (garbage extra : Mutable.Heap) :
    working base values garbage ++ extra = working base values (garbage ++ extra) := by
  simp [working, List.append_assoc]

theorem working_set (base : Mutable.Heap) (values replacement : List Constant) (garbage : Mutable.Heap) :
    (working base values garbage).set base.length (.set replacement) = working base replacement garbage := by
  simp [working, List.set_append_right]

theorem other_found (base : Mutable.Heap) (before after : List Constant) (garbage extra : Mutable.Heap)
    (address : Nat) (object : Mutable.Object) (different : address ≠ base.length)
    (found : (working base before garbage)[address]? = some object) :
    (working base after (garbage ++ extra))[address]? = some object := by
  have kept := HeapCollection.prefix_found (working base before garbage) extra address object found
  rw [working_append] at kept
  have stored := List.getElem?_set_ne (l := working base before (garbage ++ extra))
    (a := .set after) different.symm
  rw [working_set] at stored
  exact stored.trans kept

def inserted (before : List Constant) (items : List Nat) : List Constant :=
  (items.map fun (n : Nat) => Constant.int n).foldl ScalarSet.insert before

theorem inserted_append (before : List Constant) (first second : List Nat) :
    inserted before (first ++ second) = inserted (inserted before first) second := by
  simp [inserted, List.map_append, List.foldl_append]

def selected (items : List Nat) (first second : Nat) : List Nat :=
  if value (partDigits .left items first second) * value (partDigits .middle items first second) =
      value (partDigits .right items first second) then
    [value (partDigits .right items first second)] else []

def candidateBody : List Stmt :=
  [.assign [.name "a"] (partExpr .left),
   .assign [.name "b"] (partExpr .middle),
   .assign [.name "product"] (partExpr .right),
   .ifThen (.compare (.binOp (.name "a") .mult (.name "b")) [(.eq, .name "product")])
     [.expr (.call (.attribute (.name "products") "add") [.name "product"])] []]

def writes : List String := ["a", "b", "product", "first", "second"]
def Stable (before after : HeapCalls.Env) : Prop :=
  ∀ query, query ∉ writes → after query = before query

theorem candidate_result (items : List Nat) (first second address : Nat)
    (ordered : first ≤ second) (bound : second ≤ items.length)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (found : (working base before garbage)[address]? = some (.list (numbers items)))
    (getDigits : env "digits" = some (.ref address))
    (getFirst : env "first" = some (number first)) (getSecond : env "second" = some (number second))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env candidateBody (working base before garbage) finalEnv
      (working base (inserted before (selected items first second)) (garbage ++ extra)) ∧
      finalEnv "first" = some (number first) ∧ Stable env finalEnv := by
  let av := value (partDigits .left items first second)
  let bv := value (partDigits .middle items first second)
  let pv := value (partDigits .right items first second)
  let leftExtra := partExtra .left items first second
  let middleExtra := partExtra .middle items first second
  let rightExtra := partExtra .right items first second
  let heap := working base before garbage
  let e1 := setLocal env "a" (number av)
  let e2 := setLocal e1 "b" (number bv)
  let e3 := setLocal e2 "product" (number pv)
  have left : BlockContinues program env [candidateBody[0]'(by decide)] heap e1 (heap ++ leftExtra) :=
    BlockContinues.assign (part_result .left items first second address ordered bound heap found env
      getDigits getFirst getSecond)
  have middle : BlockContinues program e1 [candidateBody[1]'(by decide)]
      (heap ++ leftExtra) e2 ((heap ++ leftExtra) ++ middleExtra) :=
    BlockContinues.assign (part_result .middle items first second address ordered bound _
      (HeapCollection.prefix_found heap leftExtra address _ found) e1
      (by simpa [e1, setLocal] using getDigits) (by simpa [e1, setLocal] using getFirst)
      (by simpa [e1, setLocal] using getSecond))
  have right : BlockContinues program e2 [candidateBody[2]'(by decide)]
      ((heap ++ leftExtra) ++ middleExtra) e3 (((heap ++ leftExtra) ++ middleExtra) ++ rightExtra) :=
    BlockContinues.assign (part_result .right items first second address ordered bound _
      (HeapCollection.prefix_found (heap ++ leftExtra) middleExtra address _
        (HeapCollection.prefix_found heap leftExtra address _ found)) e2
      (by simpa [e2, e1, setLocal] using getDigits) (by simpa [e2, e1, setLocal] using getFirst)
      (by simpa [e2, e1, setLocal] using getSecond))
  let extra := leftExtra ++ middleExtra ++ rightExtra
  let readyHeap := working base before (garbage ++ extra)
  have tested : Evaluates program e3
      (.compare (.binOp (.name "a") .mult (.name "b")) [(.eq, .name "product")])
      readyHeap (flag (decide (av * bv = pv))) readyHeap := by
    apply Evaluates.compare (av := number (av * bv)) (bv := number pv)
      (middle := readyHeap) (afterRight := readyHeap)
    · exact Evaluates.binary (av := number av) (bv := number bv)
        (middle := readyHeap) (afterRight := readyHeap) (finalHeap := readyHeap)
        (Evaluates.lookup (by simp [e3, e2, e1, setLocal]))
        (Evaluates.lookup (by simp [e3, e2, setLocal])) (by simp [Mutable.binary, scalarBinary])
    · exact Evaluates.lookup (by simp [e3, setLocal])
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
      norm_cast
  have completed : BlockContinues program e3 [candidateBody[3]'(by decide)] readyHeap e3
      (working base (inserted before (selected items first second)) (garbage ++ extra)) := by
    by_cases equal : av * bv = pv
    · simp only [selected, show value (partDigits .left items first second) *
          value (partDigits .middle items first second) = value (partDigits .right items first second)
          from equal, if_true, inserted, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      apply BlockContinues.branch (middle := readyHeap) (flag := true) (value := flag true)
        (by simpa only [equal, decide_true] using tested) rfl
      apply BlockContinues.discard
      simpa only [readyHeap, working_set] using Evaluates.add (value := .int pv)
        (Evaluates.lookup (module := program) (env := e3)
          (by simpa [e3, e2, e1, setLocal] using getProducts)) (working_found base before (garbage ++ extra))
        (Evaluates.lookup (by simp [e3, setLocal])) (working_found base before (garbage ++ extra))
    · simp only [selected, show ¬ value (partDigits .left items first second) *
          value (partDigits .middle items first second) = value (partDigits .right items first second)
          from equal, if_false, inserted, List.map_nil, List.foldl_nil]
      apply BlockContinues.branch (middle := readyHeap) (flag := false) (value := flag false)
        (by simpa only [equal, decide_false] using tested) rfl
      exact .nil
  refine ⟨e3, extra, ?_, by simpa [e3, e2, e1, setLocal] using getFirst, ?_⟩
  · simp only [heap, readyHeap, extra, working, List.append_assoc]
      at left middle right completed ⊢
    exact left.append (middle.append (right.append completed))
  · intro query unchanged
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
    simp [e3, e2, e1, setLocal, unchanged.1, unchanged.2.1, unchanged.2.2.1]

end data.«project-euler-statements».data.py.project_euler_statements.p32.naive
