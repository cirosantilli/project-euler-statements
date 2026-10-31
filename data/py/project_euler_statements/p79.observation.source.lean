import data.«project-euler-statements».data.py.project_euler_statements.«p79.edges.source»
import ProjectEulerStatements.Lib.PrecedenceTriples

/-! Each reference observation allocates its three precedence pairs from Unicode characters. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev character (value : Char) : String := String.ofList [value]

def characterExpr (index : Int) : Expr := .subscript (.name "s") (.constant (.int index))

def observationExpr : Expr := .ifExp
  (.compare (.builtinCall .len [.name "s"]) [(.gtE, .constant (.int 3))])
  (.list [.tuple [characterExpr 0, characterExpr 1],
    .tuple [characterExpr 1, characterExpr 2], .tuple [characterExpr 0, characterExpr 2]])
  (.list [])

def observationEnv (s : String) : HeapCalls.Env :=
  functionEnv [{ name := "s", annotation := some (.name "str") }]
    [.return observationExpr] [text s] []

def observationEntries (address : Nat) (a b c : Char) : List Edge :=
  [(address, character a, character b), (address + 1, character b, character c),
    (address + 2, character a, character c)]

def observationHeap (heap : Mutable.Heap) (a b c : Char) : Mutable.Heap := heap ++
  [.tuple [text (character a), text (character b)],
   .tuple [text (character b), text (character c)],
   .tuple [text (character a), text (character c)],
   .list ((observationEntries heap.length a b c).map edgeValue)]

theorem observation_source : executableBody
    ((findFunctionIn program.body "edges_from").getD ([], [])).2 =
      [.return observationExpr] := rfl

theorem character_read (heap : Mutable.Heap) (env : HeapCalls.Env) (s : String)
    (getS : env "s" = some (text s)) (index : Int) (value : Char)
    (found : FormalSW.Py.Builtin.Sequence.get? s.toList index = some value) :
    Evaluates program env (characterExpr index) heap (text (character value)) heap := by
  apply Evaluates.subscript (by intros; intro impossible; cases impossible)
    (Evaluates.lookup getS) Evaluates.constant
  simp [Mutable.getItem, text, Strings.get, scalarNumber, found, character]

/-- Only the first three characters are used, even when the input has a longer suffix. -/
theorem observation_result (heap : Mutable.Heap) (s : String) (a b c : Char) (tail : List Char)
    (characters : s.toList = a :: b :: c :: tail) :
    ReturnsValue program "edges_from" [text s] heap (.ref (heap.length + 3))
      (observationHeap heap a b c) := by
  apply BlockReturns.function rfl rfl
  change BlockReturns program _ [.return observationExpr] heap _ _
  apply BlockReturns.return_value
  have length : 3 ≤ s.length := by
    have sized := congrArg List.length characters
    simp only [String.length_toList, List.length_cons] at sized
    omega
  have tested : Evaluates program (observationEnv s)
      (.compare (.builtinCall .len [.name "s"]) [(.gtE, .constant (.int 3))])
      heap (.scalar (.bool true)) heap := by
    apply Evaluates.compare (av := number s.length) (bv := number 3)
      (Evaluates.builtin (finalHeap := heap) (values := [text s])
        (.cons (Evaluates.lookup rfl) .nil)
        (by simp [primitive, Mutable.length, text])) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    omega
  apply Evaluates.conditional tested rfl
  have read (base : Mutable.Heap) (index : Int) (value : Char)
      (found : FormalSW.Py.Builtin.Sequence.get? (a :: b :: c :: tail) index = some value) :=
    character_read base (observationEnv s) s rfl index value
      (by simpa only [characters] using found)
  have first := Evaluates.tuple
    (.cons (read heap 0 a rfl) (.cons (read heap 1 b rfl) .nil)) (by simp)
  let afterFirst := heap ++ [.tuple [text (character a), text (character b)]]
  let afterSecond := afterFirst ++ [.tuple [text (character b), text (character c)]]
  have second := Evaluates.tuple
    (.cons (read afterFirst 1 b rfl) (.cons (read afterFirst 2 c rfl) .nil)) (by simp)
  have third := Evaluates.tuple
    (.cons (read afterSecond 0 a rfl) (.cons (read afterSecond 2 c rfl) .nil)) (by simp)
  simpa [observationHeap, observationEntries, List.append_assoc, afterFirst, afterSecond,
    scalarTruth, Nat.add_assoc] using
    Evaluates.list (.cons first (.cons second (.cons third .nil)))

theorem observation_represents (heap : Mutable.Heap) (a b c : Char) :
    Edges (observationHeap heap a b c) (heap.length + 3)
      (observationEntries heap.length a b c) := by
  constructor
  · simp [observationHeap]
  · intro edge member
    simp only [observationEntries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [Stored, observationHeap]

theorem observation_contents (address : Nat) (a b c : Char) :
    (observationEntries address a b c).map Prod.snd =
      ProjectEulerStatements.TopologicalOrder.expandedEdges
        [(character a, character b, character c)] := rfl

theorem observation_short (heap : Mutable.Heap) (s : String) (short : s.length < 3) :
    ReturnsValue program "edges_from" [text s] heap (.ref heap.length)
      (heap ++ [.list []]) := by
  apply BlockReturns.function rfl rfl
  change BlockReturns program _ [.return observationExpr] heap _ _
  apply BlockReturns.return_value
  have tested : Evaluates program (observationEnv s)
      (.compare (.builtinCall .len [.name "s"]) [(.gtE, .constant (.int 3))])
      heap (.scalar (.bool false)) heap := by
    apply Evaluates.compare (av := number s.length) (bv := number 3)
      (Evaluates.builtin (finalHeap := heap) (values := [text s])
        (.cons (Evaluates.lookup rfl) .nil)
        (by simp [primitive, Mutable.length, text])) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    omega
  exact Evaluates.conditional tested rfl (Evaluates.list .nil)

end data.«project-euler-statements».data.py.project_euler_statements.p79
