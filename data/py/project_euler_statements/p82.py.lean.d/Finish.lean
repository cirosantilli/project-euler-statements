import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Rows

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev outerFor : Stmt := .forIn (.name "col")
  (.subscript (.name "cols") (.slice (some (.constant (.int 1))) none none)) outerBody []
abbrev columnsTail : List Stmt :=
  [.ifThen (.unaryOp .not (.name "cols")) [.return (.constant (.int 0))] [],
   .assign [.name "final"] (.subscript (.name "cols") (.constant (.int 0))), outerFor, .return minimumOrZero]

def columnsValue (rows : MatrixRows) : Int :=
  match rows.map Prod.snd with
  | [] => 0
  | first :: rest => minimum (rest.foldl columnStep first)

theorem finish_columns (heap : Mutable.Heap) (env : HeapCalls.Env) (address height : Nat) (rows : MatrixRows)
    (contents : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (shape : ∀ pair ∈ rows, pair.2.length = height) (localCols : env "cols" = some (.ref address)) :
    ∃ extra, BlockReturns program env columnsTail heap (number (columnsValue rows)) (heap ++ extra) := by
  have tested : Evaluates program env (.unaryOp .not (.name "cols")) heap
      (.scalar (.bool (decide (rows = [])))) heap :=
    Evaluates.unary (Evaluates.lookup localCols)
      (by simp [HeapCalls.unary, Mutable.truth, contents]; cases rows <;> rfl)
  cases rows with
  | nil =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil, columnsValue, List.map_nil]
      apply BlockReturns.branch (flag := true) tested rfl
      exact BlockReturns.return_value Evaluates.constant
  | cons first rest =>
      have firstValue : Evaluates program env (.subscript (.name "cols") (.constant (.int 0))) heap (.ref first.1) heap := by
        apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup localCols) Evaluates.constant
        simp [Mutable.getItem, Mutable.index, contents, Except.map]
      let ready := setLocal env "final" (.ref first.1)
      let refs := rest.map (fun pair => Mutable.Value.ref pair.1)
      let sliced := heap ++ [.list refs]
      have slice : Evaluates program ready (.subscript (.name "cols") (.slice (some (.constant (.int 1))) none none))
          heap (.ref heap.length) sliced := by
        apply Evaluates.slice (.cons (Evaluates.lookup (by simpa [ready, setLocal] using localCols))
          (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
        simpa [sliced, refs] using Mutable.getSlice_list_suffix heap address
          ((first :: rest).map (fun pair => .ref pair.1)) 1 contents
      have kept (address : Nat) (object : Mutable.Object) (found : heap[address]? = some object) :
          sliced[address]? = some object := by
        unfold sliced
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
        exact found
      have source : sliced[heap.length]? = some (.list refs) := by simp [sliced]
      obtain ⟨extra, loop⟩ := rows_loop sliced ready heap.length 0 first.1 height rest first.2 source
        (fun pair member => kept _ _ (reads pair (by simp [member])))
        (fun pair member => shape pair (by simp [member])) (shape first (by simp))
        (kept _ _ (reads first (by simp))) rfl
      refine ⟨[.list refs] ++ extra, ?_⟩
      apply BlockReturns.branch (flag := false) tested rfl
      apply BlockReturns.assign firstValue
      apply BlockReturns.for_sequence (items := refs) (by intros expressions impossible; cases impossible) slice
        (by simp [Mutable.sequence, source])
      simpa [columnsValue, sliced, List.append_assoc] using loop

end data.«project-euler-statements».data.py.project_euler_statements.p82
