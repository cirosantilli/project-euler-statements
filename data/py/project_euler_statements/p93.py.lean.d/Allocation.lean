import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Expressions

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
set_option Elab.async false

abbrev firstPairs (a b : Pair) := [add a b, sub a b, mul a b]
abbrev firstObjects (a b : Pair) := (firstPairs a b).map object
abbrev firstRefs (base : Mutable.Heap) : List Mutable.Value :=
  [.ref base.length, .ref (base.length + 1), .ref (base.length + 2)]
abbrev listAddress (base : Mutable.Heap) := base.length + 3

def initialHeap (base : Mutable.Heap) (a b : Pair) : Mutable.Heap :=
  base ++ (firstObjects a b ++ [.list (firstRefs base)])

def extendedHeap (base : Mutable.Heap) (a b pair : Pair) : Mutable.Heap :=
  base ++ (firstObjects a b ++ [.list (firstRefs base ++ [.ref (base.length + 4)]), object pair])

@[simp] theorem initial_length (base : Mutable.Heap) (a b : Pair) :
    (initialHeap base a b).length = base.length + 4 := by simp [initialHeap]

@[simp] theorem initial_list (base : Mutable.Heap) (a b : Pair) :
    (initialHeap base a b)[listAddress base]? = some (.list (firstRefs base)) := by simp [initialHeap]

@[simp] theorem extended_list (base : Mutable.Heap) (a b pair : Pair) :
    (extendedHeap base a b pair)[listAddress base]? = some (.list (firstRefs base ++ [.ref (base.length+4)])) := by
  simp [extendedHeap]

/-- The initial three tuples and their enclosing list are fresh, in source evaluation order. -/
theorem initial (a b : Pair) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (ready : Ready env a b) :
    Evaluates program env (.list [addExpr, subExpr, mulExpr]) heap (.ref (listAddress heap))
      (initialHeap heap a b) globals := by
  have first := addition (heap := heap) (globals := globals) a b ready
  have second := subtraction (heap := heap ++ [object (add a b)]) (globals := globals) a b ready
  have third := multiplication (heap := (heap ++ [object (add a b)]) ++ [object (sub a b)])
    (globals := globals) a b ready
  have built := Evaluates.list (Evaluates.Arguments.cons first (.cons second (.cons third .nil)))
  simpa [initialHeap, List.append_assoc] using built

theorem initial_found (base : Mutable.Heap) (a b : Pair) :
    Heap.ListFound (initialHeap base a b) (listAddress base) (firstPairs a b) := by
  refine ⟨firstRefs base, initial_list base a b, .cons ?_ (.cons ?_ (.cons ?_ .nil))⟩
  · exact ⟨base.length, rfl, by simp [initialHeap]⟩
  · exact ⟨base.length+1, rfl, by simp [initialHeap]⟩
  · exact ⟨base.length+2, rfl, by simp [initialHeap]⟩

theorem extended_found (base : Mutable.Heap) (a b pair : Pair) :
    Heap.ListFound (extendedHeap base a b pair) (listAddress base) (firstPairs a b ++ [pair]) := by
  refine ⟨firstRefs base ++ [.ref (base.length+4)], extended_list base a b pair,
    .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))⟩
  · exact ⟨base.length, rfl, by simp [extendedHeap]⟩
  · exact ⟨base.length+1, rfl, by simp [extendedHeap]⟩
  · exact ⟨base.length+2, rfl, by simp [extendedHeap]⟩
  · exact ⟨base.length+4, rfl, by simp [extendedHeap]⟩

/-- Appending a quotient only writes the private output list. -/
theorem append_pair (a b pair : Pair) (base : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (expression : Expr)
    (out : env "out" = some (.ref (listAddress base)))
    (evaluated : Evaluates program env expression (initialHeap base a b)
      (.ref (initialHeap base a b).length) (initialHeap base a b ++ [object pair]) globals) :
    BlockReturns program env [.expr (.call (.attribute (.name "out") "append") [expression]), .return (.name "out")]
      (initialHeap base a b) (.ref (listAddress base)) (extendedHeap base a b pair) globals := by
  have retained : (initialHeap base a b ++ [object pair])[listAddress base]? = some (.list (firstRefs base)) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ _ _ _ (initial_list base a b)
  have appended := Evaluates.append (Evaluates.lookup out) (initial_list base a b) evaluated retained
  have final : (initialHeap base a b ++ [object pair]).set (listAddress base)
      (.list (firstRefs base ++ [.ref (initialHeap base a b).length])) = extendedHeap base a b pair := by
    simp [initialHeap, extendedHeap, List.set_append_right, List.append_assoc]
  rw [final] at appended
  exact BlockReturns.discard appended (BlockReturns.return_value (Evaluates.lookup out))

end data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
