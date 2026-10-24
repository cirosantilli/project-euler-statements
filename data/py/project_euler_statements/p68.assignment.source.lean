import data.«project-euler-statements».data.py.project_euler_statements.«p68.lines.source»
import ProjectEulerStatements.Lib.MagicRingMinimumCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p68
open FormalSW.PyAst HeapCalls ProjectEulerStatements MagicRingTextCalls
set_option Elab.async false

abbrev outerExpression : Expr :=
  .builtinCall .list [.subscript (.name "values") (.slice none (some (.name "n")) none)]
abbrev innerExpression : Expr :=
  .subscript (.name "values") (.slice (some (.name "n")) none none)
abbrev splitCode : List Stmt :=
  [.assign [.name "outer"] outerExpression, .assign [.name "inner"] innerExpression]

theorem split_code_source : permutationBody.take 2 = splitCode := rfl

def splitHeap {n : Nat} (base : Mutable.Heap) (ring : MagicRing.Ring n) : Mutable.Heap :=
  base ++ [.tuple (encode ring.outer), .list (encode ring.outer), .tuple (encode ring.inner)]
def splitEnv (base : Mutable.Heap) (env : HeapCalls.Env) : HeapCalls.Env :=
  setLocal (setLocal env "outer" (.ref (base.length + 1))) "inner" (.ref (base.length + 2))

theorem split_result {n : Nat} (ring : MagicRing.Ring n) (positive : 0 < n)
    (base : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (contents : base[address]? = some (.tuple (encode (ring.outer ++ ring.inner))))
    (localValues : env "values" = some (.ref address)) (localN : env "n" = some (number n)) :
    BlockContinues program env splitCode base (splitEnv base env) (splitHeap base ring) := by
  let sliced := base ++ [.tuple (encode ring.outer)]
  let copied := base ++ [.tuple (encode ring.outer), .list (encode ring.outer)]
  let outerEnv := setLocal env "outer" (.ref (base.length + 1))
  have outerPresent : (encode ring.outer).isEmpty = false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro empty
    have length := congrArg List.length empty
    simp [encode, ring.outer_length] at length
    omega
  have innerPresent : (encode ring.inner).isEmpty = false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro empty
    have length := congrArg List.length empty
    simp [encode, ring.inner_length] at length
    omega
  have firstSlice : Evaluates program env
      (.subscript (.name "values") (.slice none (some (.name "n")) none))
      base (.ref base.length) sliced := by
    apply Evaluates.slice
      (.cons (Evaluates.lookup localValues) (.cons Evaluates.constant
        (.cons (Evaluates.lookup localN) (.cons Evaluates.constant .nil))))
    have slice := Mutable.getSlice_tuple_prefix base address (encode (ring.outer ++ ring.inner)) n
      (by simp [encode, ring.outer_length, ring.inner_length]; omega) contents
    have selectedPrefix : (encode (ring.outer ++ ring.inner)).take n = encode ring.outer := by
      simp only [encode, ← List.map_take, ← ring.outer_length, List.take_left]
    simpa [selectedPrefix, Mutable.allocateTuple, outerPresent, sliced, Except.map] using slice
  have copiedOuter : Evaluates program env outerExpression base
      (.ref (base.length + 1)) copied := by
    apply Evaluates.builtin (.cons firstSlice .nil)
    simp [HeapCalls.primitive, Mutable.sequence, sliced, copied, Mutable.allocate,
      List.append_assoc, Except.map]
  have readValues : copied[address]? = some (.tuple (encode (ring.outer ++ ring.inner))) := by
    dsimp [copied]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp contents).1]
    exact contents
  have lastSlice : Evaluates program outerEnv innerExpression copied
      (.ref (base.length + 2)) (splitHeap base ring) := by
    apply Evaluates.slice
      (.cons (Evaluates.lookup (by simpa [outerEnv, setLocal] using localValues))
        (.cons (Evaluates.lookup (by simpa [outerEnv, setLocal] using localN))
          (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    have slice := Mutable.getSlice_tuple_suffix copied address (encode (ring.outer ++ ring.inner)) n
      positive (by simp [encode, ring.outer_length, ring.inner_length]) readValues
    have suffix : (encode (ring.outer ++ ring.inner)).drop n = encode ring.inner := by
      simp only [encode, ← List.map_drop, ← ring.outer_length, List.drop_left]
    simpa [suffix, Mutable.allocateTuple, innerPresent, copied, splitHeap,
      List.append_assoc, Except.map] using slice
  exact (BlockContinues.assign copiedOuter).append (BlockContinues.assign lastSlice)

theorem split_outer {n : Nat} (base : Mutable.Heap) (ring : MagicRing.Ring n) :
    (splitHeap base ring)[base.length + 1]? = some (.list (encode ring.outer)) := by
  simp [splitHeap]

theorem split_inner {n : Nat} (base : Mutable.Heap) (ring : MagicRing.Ring n) :
    (splitHeap base ring)[base.length + 2]? = some (.tuple (encode ring.inner)) := by
  simp [splitHeap]

end data.«project-euler-statements».data.py.project_euler_statements.p68
