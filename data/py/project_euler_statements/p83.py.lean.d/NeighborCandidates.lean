import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Read
import lang.py.FormalSW.ComprehensionCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.TriangleBufferCalls (number)
set_option Elab.async false

abbrev pairFields (pair : Int × Int) : List Mutable.Value := [number pair.1, number pair.2]
abbrev candidates (r c : Int) : List (Int × Int) := [(r + 1, c), (r, c + 1), (r, c - 1), (r - 1, c)]
abbrev candidateExpressions : List Expr :=
  [.tuple [.binOp (.name "r") .add (.constant (.int 1)), .name "c"],
   .tuple [.name "r", .binOp (.name "c") .add (.constant (.int 1))],
   .tuple [.name "r", .binOp (.name "c") .sub (.constant (.int 1))],
   .tuple [.binOp (.name "r") .sub (.constant (.int 1)), .name "c"]]
def candidateRefs (heap : Mutable.Heap) : List Mutable.Value :=
  [.ref heap.length, .ref (heap.length + 1), .ref (heap.length + 2), .ref (heap.length + 3)]
def candidateHeap (heap : Mutable.Heap) (r c : Int) : Mutable.Heap :=
  heap ++ (candidates r c).map (fun pair => .tuple (pairFields pair)) ++ [.list (candidateRefs heap)]

theorem candidate_allocation (heap : Mutable.Heap) (env : HeapCalls.Env) (r c : Int)
    (localRow : env "r" = some (number r)) (localCol : env "c" = some (number c)) :
    Evaluates program env (.list candidateExpressions) heap (.ref (heap.length + 4)) (candidateHeap heap r c) := by
  have down (state : Mutable.Heap) : Evaluates program env candidateExpressions[0] state (.ref state.length)
      (state ++ [.tuple (pairFields (r + 1, c))]) :=
    Evaluates.tuple (.cons (Evaluates.binary (Evaluates.lookup localRow) Evaluates.constant rfl)
      (.cons (Evaluates.lookup localCol) .nil)) (by simp)
  have right (state : Mutable.Heap) : Evaluates program env candidateExpressions[1] state (.ref state.length)
      (state ++ [.tuple (pairFields (r, c + 1))]) :=
    Evaluates.tuple (.cons (Evaluates.lookup localRow)
      (.cons (Evaluates.binary (Evaluates.lookup localCol) Evaluates.constant rfl) .nil)) (by simp)
  have left (state : Mutable.Heap) : Evaluates program env candidateExpressions[2] state (.ref state.length)
      (state ++ [.tuple (pairFields (r, c - 1))]) :=
    Evaluates.tuple (.cons (Evaluates.lookup localRow)
      (.cons (Evaluates.binary (Evaluates.lookup localCol) Evaluates.constant rfl) .nil)) (by simp)
  have up (state : Mutable.Heap) : Evaluates program env candidateExpressions[3] state (.ref state.length)
      (state ++ [.tuple (pairFields (r - 1, c))]) :=
    Evaluates.tuple (.cons (Evaluates.binary (Evaluates.lookup localRow) Evaluates.constant rfl)
      (.cons (Evaluates.lookup localCol) .nil)) (by simp)
  have listed := Evaluates.list (.cons (down heap) (.cons (right _) (.cons (left _) (.cons (up _) .nil))))
  simpa [candidateHeap, candidateRefs, List.append_assoc] using listed

abbrev neighborFilter : Expr := .boolOp .and
  [.compare (.name "rr") [(.gtE, .constant (.int 0))],
   .compare (.name "cc") [(.gtE, .constant (.int 0))],
   .compare (.name "rr") [(.lt, .name "rows")],
   .compare (.name "cc") [(.lt, .name "cols")]]

theorem neighbor_filter (heap : Mutable.Heap) (env : HeapCalls.Env) (r c : Int) (height width : Nat)
    (localRow : env "rr" = some (number r)) (localCol : env "cc" = some (number c))
    (localHeight : env "rows" = some (number height)) (localWidth : env "cols" = some (number width)) :
    Evaluates program env neighborFilter heap
      (.scalar (.bool (decide (0 ≤ r ∧ 0 ≤ c ∧ r < height ∧ c < width)))) heap := by
  have lowerR : Evaluates program env (.compare (.name "rr") [(.gtE, .constant (.int 0))]) heap
      (.scalar (.bool (decide (0 ≤ r)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localRow) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have lowerC : Evaluates program env (.compare (.name "cc") [(.gtE, .constant (.int 0))]) heap
      (.scalar (.bool (decide (0 ≤ c)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localCol) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have upperR : Evaluates program env (.compare (.name "rr") [(.lt, .name "rows")]) heap
      (.scalar (.bool (decide (r < height)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localRow) (Evaluates.lookup localHeight)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have upperC : Evaluates program env (.compare (.name "cc") [(.lt, .name "cols")]) heap
      (.scalar (.bool (decide (c < width)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localCol) (Evaluates.lookup localWidth)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases hr : 0 ≤ r
  · simp only [hr, true_and]
    apply Evaluates.boolean_next (flag := true) (value := .scalar (.bool true))
      (by simpa only [hr, decide_true] using lowerR) rfl rfl
    by_cases hc : 0 ≤ c
    · simp only [hc, true_and]
      apply Evaluates.boolean_next (flag := true) (value := .scalar (.bool true))
        (by simpa only [hc, decide_true] using lowerC) rfl rfl
      by_cases ur : r < height
      · simp only [ur, true_and]
        apply Evaluates.boolean_next (flag := true) (value := .scalar (.bool true))
          (by simpa only [ur, decide_true] using upperR) rfl rfl
        exact Evaluates.boolean_last upperC rfl
      · simp only [ur, false_and, decide_false]
        exact Evaluates.boolean_stop (by simpa only [ur, decide_false] using upperR) rfl rfl
    · simp only [hc, false_and, decide_false]
      exact Evaluates.boolean_stop (by simpa only [hc, decide_false] using lowerC) rfl rfl
  · simp only [hr, false_and, decide_false]
    exact Evaluates.boolean_stop (by simpa only [hr, decide_false] using lowerR) rfl rfl

end data.«project-euler-statements».data.py.project_euler_statements.p83
