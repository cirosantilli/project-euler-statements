import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Operations
import lang.py.FormalSW.ListExtensionCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

abbrev program := P93Ast.module
abbrev collect : List Stmt :=
  [.expr (.call (.attribute (.name "out") "extend") [.call (.name "eval_ops") [.name "a", .name "b"]])]

/-- One source combination appends every operation result, retaining earlier result tuples. -/
theorem collect_result (base : Mutable.Heap) (old : List Mutable.Value) (garbage : Mutable.Heap)
    (pairs : List Pair) (a b : Pair) (left right : Mutable.Value) (env : HeapCalls.Env)
    (globals : Mutable.Globals)
    (rows : Heap.Rows (working base old garbage) old pairs)
    (rowA : Heap.Row (working base old garbage) left a)
    (rowB : Heap.Row (working base old garbage) right b)
    (getOut : env "out" = some (.ref base.length))
    (getA : env "a" = some left) (getB : env "b" = some right) :
    ∃ additional extra,
      BlockContinues program env collect (working base old garbage) env
        (working base (old ++ additional) (garbage ++ extra)) globals ∧
      Heap.Rows (working base (old ++ additional) (garbage ++ extra))
        (old ++ additional) (pairs ++ reference a b) := by
  obtain ⟨leftAddress, rfl, foundA⟩ := rowA
  obtain ⟨rightAddress, rfl, foundB⟩ := rowB
  obtain ⟨extra, evaluated, additional, foundList, added⟩ :=
    eval_ops.result a b leftAddress rightAddress (working base old garbage) globals foundA foundB
  have called : Evaluates program env (.call (.name "eval_ops") [.name "a", .name "b"])
      (working base old garbage) (.ref (eval_ops.listAddress (working base old garbage)))
      (working base old garbage ++ extra) globals :=
    Evaluates.call (.cons (Evaluates.lookup getA) (.cons (Evaluates.lookup getB) .nil)) evaluated
  have destination : (working base old garbage ++ extra)[base.length]? = some (.list old) := by
    rw [append]
    exact found base old (garbage ++ extra)
  have extended := Evaluates.extendList (Evaluates.lookup getOut) (found base old garbage)
    (.cons called .nil) (extendList_list _ _ _ _ _ destination foundList)
    (by intro name same; cases same; simp [getOut])
  refine ⟨additional, extra, ?_, ?_⟩
  · simpa only [append, store] using BlockContinues.discard extended
  · have kept := rows.collector (old ++ additional) extra
    have newRows : Heap.Rows (working base old (garbage ++ extra)) additional (reference a b) := by
      simpa only [append] using added
    have newKept := newRows.collector (old ++ additional) []
    simp only [List.append_nil] at newKept
    exact List.rel_append kept newKept

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
