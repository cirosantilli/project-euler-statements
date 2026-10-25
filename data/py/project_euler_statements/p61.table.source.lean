import data.«project-euler-statements».data.py.project_euler_statements.«p61.search.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p61.families.source»
import lang.py.FormalSW.ComprehensionCalls

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.table
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
open extend (numbers)
private abbrev program := P61Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)

def lookup : List (Int × Nat) → Int → Option Nat
  | [], _ => none
  | (stored, address) :: rest, key => if stored = key then some address else lookup rest key

def put : List (Int × Nat) → Int → Nat → List (Int × Nat)
  | [], key, address => [(key, address)]
  | (stored, old) :: rest, key, address =>
      if stored = key then (stored, address) :: rest else (stored, old) :: put rest key address

def encode (entries : List (Int × Nat)) : List (Constant × Mutable.Value) :=
  entries.map (fun (key, address) => (.int key, .ref address))

theorem lookup_encode (entries : List (Int × Nat)) (key : Int) :
    ScalarDict.lookup (encode entries) (.int key) = (lookup entries key).map Mutable.Value.ref := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨stored, address⟩ := entry
      by_cases same : stored = key
      · simp [encode, lookup, ScalarDict.lookup, scalarCompare, evalCmpOp, same]
      · simpa [encode, lookup, ScalarDict.lookup, scalarCompare, evalCmpOp, same] using ih

theorem encode_put (entries : List (Int × Nat)) (key : Int) (address : Nat) :
    ScalarDict.insert (encode entries) (.int key) (.ref address) = encode (put entries key address) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨stored, old⟩ := entry
      by_cases same : stored = key
      · simp [encode, put, ScalarDict.insert, scalarCompare, evalCmpOp, same]
      · simpa [encode, put, ScalarDict.insert, scalarCompare, evalCmpOp, same] using
          congrArg (fun result : List (Constant × Mutable.Value) => (.int stored, .ref old) :: result) ih

theorem lookup_put_self (entries : List (Int × Nat)) (key : Int) (address : Nat) :
    lookup (put entries key address) key = some address := by
  induction entries with
  | nil => simp [put, lookup]
  | cons entry rest ih =>
      obtain ⟨stored, old⟩ := entry
      by_cases same : stored = key <;> simp [put, lookup, same, ih]

theorem lookup_put_other (entries : List (Int × Nat)) (key query : Int) (address : Nat)
    (different : key ≠ query) : lookup (put entries key address) query = lookup entries query := by
  induction entries with
  | nil => simp [put, lookup, different]
  | cons entry rest ih =>
      obtain ⟨stored, old⟩ := entry
      by_cases same : stored = key
      · subst stored
        simp [put, lookup, different]
      · by_cases selected : stored = query
        · subst stored
          simp [put, lookup, Ne.symm different]
        · simp [put, lookup, same, selected, ih]

/-- The fresh dictionary owns complete family lists and preserves the caller's heap prefix. -/
structure Store (base heap : Mutable.Heap) (processed : List Int) where
  entries : List (Int × Nat)
  extension : ∃ extra, heap = base ++ extra
  table : heap[base.length]? = some (.dict (encode entries))
  present : ∀ kind ∈ processed, ∃ address, base.length < address ∧
    lookup entries kind = some address ∧ heap[address]? = some (.list (numbers (PolygonalFamilies.family kind)))

def Store.initial (base : Mutable.Heap) : Store base (base ++ [.dict []]) [] where
  entries := []
  extension := ⟨[.dict []], rfl⟩
  table := by simp [encode]
  present := by simp

private theorem extension_set (base heap : Mutable.Heap)
    (extension : ∃ extra, heap = base ++ extra) (address : Nat) (outside : base.length ≤ address)
    (object : Mutable.Object) : ∃ extra, heap.set address object = base ++ extra := by
  obtain ⟨extra, rfl⟩ := extension
  exact ⟨extra.set (address - base.length) object, List.set_append_right address object outside⟩

variable {base heap : Mutable.Heap} {processed : List Int}

def storedHeap (base heap : Mutable.Heap) (entries : List (Int × Nat)) (sides : Int) : Mutable.Heap :=
  (heap ++ [Mutable.Object.list (numbers (PolygonalFamilies.family sides))]).set base.length
    (.dict (encode (put entries sides heap.length)))

def Store.add (store : Store base heap processed) (sides : Int) :
    Store base (storedHeap base heap store.entries sides) (processed ++ [sides]) where
  entries := put store.entries sides heap.length
  extension := by
    apply extension_set base _ ?_ base.length (by rfl)
    obtain ⟨extra, same⟩ := store.extension
    exact ⟨extra ++ [.list (numbers (PolygonalFamilies.family sides))], by rw [same, List.append_assoc]⟩
  table := by
    apply List.getElem?_set_self
    have inside := (List.getElem?_eq_some_iff.mp store.table).1
    simp only [List.length_append, List.length_singleton]
    omega
  present := by
    intro kind member
    have inside := (List.getElem?_eq_some_iff.mp store.table).1
    by_cases same : kind = sides
    · subst kind
      refine ⟨heap.length, by omega, lookup_put_self _ _ _, ?_⟩
      unfold storedHeap
      rw [List.getElem?_set_ne (by omega : base.length ≠ heap.length)]
      simp
    · have old : kind ∈ processed := by simpa [same] using member
      obtain ⟨address, outside, looked, found⟩ := store.present kind old
      refine ⟨address, outside, ?_, ?_⟩
      · rw [lookup_put_other _ _ _ _ (Ne.symm same), looked]
      · unfold storedHeap
        rw [List.getElem?_set_ne (by omega : base.length ≠ address)]
        exact HeapCollection.prefix_found _ _ _ _ found

def valueExpression : Expr := .call (.name "four_digit") [.name "sides"]
def body (address : Nat) : List Stmt := [.comprehensionStore address (.name "sides") valueExpression]

theorem store_result (store : Store base heap processed) (sides : Int) (valid : 3 ≤ sides)
    (env : HeapCalls.Env) (getSides : env "sides" = some (number sides))
    (globals : Mutable.Globals := []) :
    BlockContinues program env (body base.length) heap env (storedHeap base heap store.entries sides) globals := by
  have evaluated : Evaluates program env valueExpression heap (.ref heap.length)
      (heap ++ [.list (numbers (PolygonalFamilies.family sides))]) globals :=
    Evaluates.call (.cons (Evaluates.lookup getSides) .nil) (four_digit.result sides valid heap globals)
  have tableFound := HeapCollection.prefix_found heap [.list (numbers (PolygonalFamilies.family sides))]
    base.length _ store.table
  apply BlockContinues.comprehension_store (.cons (Evaluates.lookup getSides) (.cons evaluated .nil))
  simpa only [storedHeap, encode_put] using
    Mutable.setItem_dictionary _ _ _ tableFound (.int sides) (.ref heap.length)

theorem range_loop (first count stop : Nat) (valid : 3 ≤ first) (endpoint : first + count = stop)
    (store : Store base heap processed) (env : HeapCalls.Env) (globals : Mutable.Globals := []) :
    ∃ (finalHeap : Mutable.Heap) (finalEnv : HeapCalls.Env) (_finalStore : Store base finalHeap
        (processed ++ (List.range' first count).map (fun (n : Nat) => (n : Int)))),
      BlockContinues program env [.rangeStepLoop "sides" first stop 1 (body base.length) []]
        heap finalEnv finalHeap globals := by
  induction count generalizing first heap processed env with
  | zero =>
      refine ⟨heap, env, ?_, ?_⟩
      · simpa only [List.range'_zero, List.map_nil, List.append_nil] using store
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "sides" (number first)
      have generated := store_result store first (by omega) bound rfl globals
      obtain ⟨finalHeap, finalEnv, finalStore, executed⟩ := ih (first + 1) (by omega) (by omega)
        (store.add first) bound
      refine ⟨finalHeap, finalEnv, ?_, ?_⟩
      · simpa only [List.range'_succ, List.map_cons, List.append_assoc, List.singleton_append] using finalStore
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using generated.append executed

def generators : List (Expr × Expr × List Expr) :=
  [(.name "sides", .call (.name "range")
    [.constant (.int 3), .binOp (.name "max_sides") .add (.constant (.int 1))], [])]
def expression : Expr := .dictComp (.name "sides") valueExpression generators

theorem result (maxSides : Nat) (large : 3 ≤ maxSides) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getMax : env "max_sides" = some (number maxSides)) (globals : Mutable.Globals := []) :
    ∃ (finalHeap : Mutable.Heap) (_store : Store heap finalHeap
        ((List.range' 3 (maxSides - 2)).map (fun (kind : Nat) => (kind : Int)))),
      Evaluates program env expression heap (.ref heap.length) finalHeap globals := by
  obtain ⟨finalHeap, finalEnv, store, executed⟩ := range_loop 3 (maxSides - 2) (maxSides + 1)
    (by decide) (by omega) (Store.initial heap) (comprehensionTargetsEnv env generators) globals
  refine ⟨finalHeap, by simpa only [List.nil_append] using store, ?_⟩
  apply Evaluates.dict_comp_range (values := [number 3, number (maxSides + 1)])
    (.cons Evaluates.constant (.cons (Evaluates.binary (av := number maxSides) (bv := number 1)
      (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup getMax) Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil)) rfl
  simpa only [generators, comprehensionTargetName, comprehensionTargetBody, comprehensionFilters,
    List.foldr_nil, comprehensionTargetsBody, body] using executed

/-- Capturing the completed dictionary produces the read-only world required by every recursive call. -/
theorem Store.world (store : Store base heap processed) (maxSides : Int)
    (covered : ∀ kind, 3 ≤ kind ∧ kind ≤ maxSides → kind ∈ processed) :
    Nonempty (extend.World (heap ++ [.list [.ref base.length]]) heap.length maxSides) := by
  refine ⟨{
    table := base.length
    target := fun kind => (lookup store.entries kind).getD 0
    entries := encode store.entries
    cellFound := by simp
    tableFound := HeapCollection.prefix_found _ _ _ _ store.table
    looked := ?_
    familyFound := ?_
  }⟩
  · intro kind valid
    obtain ⟨address, _, looked, _⟩ := store.present kind (covered kind valid)
    simp only [lookup_encode, looked, Option.map_some, Option.getD_some]
  · intro kind valid
    obtain ⟨address, _, looked, found⟩ := store.present kind (covered kind valid)
    simpa only [looked, Option.getD_some] using HeapCollection.prefix_found heap [.list [.ref base.length]]
      address _ found

end data.«project-euler-statements».data.py.project_euler_statements.p61.table
