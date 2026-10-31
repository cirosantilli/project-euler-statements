import data.«project-euler-statements».data.py.project_euler_statements.«p79.filter.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.choose.source»
import ProjectEulerStatements.Lib.StringSorting

/-! Sorting and filtering the reference node list preserve the least-ready selection invariant. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def nodeFilterTest : Expr := .compare (.name "n") [(.notEq, .name "found")]
def nodeFilter : Expr := .listComp (.name "n") [("n", .name "ns", [nodeFilterTest])]

theorem node_filter_source : (match (topoCode[2]? : Option Stmt) with
    | some (Stmt.whileDo _ body _) => body[3]?
    | _ => none) = some (.assign [.name "ns"] nodeFilter) := rfl

theorem node_filter_result (base : Mutable.Heap) (address : Nat) (nodes : List String)
    (found : base[address]? = some (.list (nodes.map text)))
    (env : HeapCalls.Env) (node : String) (getNodes : env "ns" = some (.ref address))
    (getFound : env "found" = some (text node)) :
    Evaluates program env nodeFilter base (.ref base.length)
      (base ++ [.list ((nodes.filter (fun item => decide (item ≠ node))).map text)]) := by
  let inner := comprehensionEnv env [("n", .name "ns", [nodeFilterTest])]
  let invariant := fun current : HeapCalls.Env => current "found" = some (text node)
  have valid : invariant inner := by
    simpa [invariant, inner, comprehensionEnv, setLocal] using getFound
  obtain ⟨finalEnv, filtered, _⟩ := filter_loop base address nodes text
    (fun item => decide (item ≠ node)) nodeFilterTest "n" found invariant
    (by intro current item bound; simpa [invariant, setLocal] using bound)
    (by
      intro current item collected bound _ lookup
      apply Evaluates.compare (Evaluates.lookup lookup) (Evaluates.lookup bound)
      simp [HeapCalls.compare, scalarCompare]) [] nodes [] rfl inner valid
  apply Evaluates.list_comp_sequence (items := nodes.map text)
    (by intros; intro impossible; cases impossible) (Evaluates.lookup getNodes)
    (by simp [Mutable.sequence, found])
  simpa only [List.length_nil, List.nil_append] using filtered

theorem node_filter_erase (nodes : List String) (node : String) (unique : nodes.Nodup) :
    nodes.filter (fun item => decide (item ≠ node)) = nodes.erase node := by
  rw [unique.erase_eq_filter]
  congr 1
  funext item
  simp [bne, beq_eq_decide]

theorem node_filter_sorted (nodes : List String) (node : String)
    (sorted : nodes.Pairwise (· ≤ ·)) :
    (nodes.filter (fun item => decide (item ≠ node))).Pairwise (· ≤ ·) :=
  sorted.sublist List.filter_sublist

theorem sort_nodes_result (heap : Mutable.Heap) (address : Nat) (nodes : List String)
    (found : heap[address]? = some (.list (nodes.map text)))
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref address)) :
    Evaluates program env (.builtinCall .sorted [.name "ns"]) heap (.ref heap.length)
      (heap ++ [.list ((ScalarSort.strings nodes).map text)]) := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getNodes) .nil)
  have sorted := primitive_sorted_list heap address (nodes.map Constant.string)
    ((ScalarSort.strings nodes).map Constant.string)
    (by simpa [List.map_map, Function.comp_def] using found) (ScalarSort.sort_strings nodes)
  simpa [List.map_map, Function.comp_def] using sorted

end data.«project-euler-statements».data.py.project_euler_statements.p79
