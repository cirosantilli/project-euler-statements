import data.«project-euler-statements».data.py.project_euler_statements.«p61.starts.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
private abbrev program := P61Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

def sourceCode : List Stmt :=
  [.ifThen (.compare (.name "max_sides") [(.lt, .constant (.int 3))]) [.return (.constant (.int 0))] [],
   .assign [.name "__formalsw_cell_naive_families"] (.list [table.expression]),
   .assign [.name "best"] (.constant (.int 0)),
   .forIn (.name "start") startIterable startBody [], .return (.name "best")]

theorem code_source :
    executableBody ((findFunctionIn program.body "naive").getD ([], [])).2 = sourceCode := rfl

theorem positive_result (maxSides : Nat) (large : 3 ≤ maxSides) (caller : Mutable.Heap)
    (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number maxSides] caller
      (number (PolygonalCycleSearch.reference PolygonalFamilies.family maxSides)) (caller ++ extra) globals := by
  let params := ((findFunctionIn program.body "naive").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
  let env := functionEnv params sourceBody [number maxSides] globals
  have getMax : env "max_sides" = some (number maxSides) := by cases globals <;> rfl
  obtain ⟨built, store, generated⟩ := table.result maxSides large caller env getMax globals
  have covered : ∀ kind : Int, 3 ≤ kind ∧ kind ≤ maxSides →
      kind ∈ (List.range' 3 (maxSides - 2)).map (fun (n : Nat) => (n : Int)) := by
    intro kind bounds
    apply List.mem_map.mpr
    refine ⟨kind.toNat, List.mem_range'_1.mpr ⟨by omega, by omega⟩, by omega⟩
  obtain ⟨world⟩ := store.world maxSides covered
  let captured := setLocal env "__formalsw_cell_naive_families" (.ref built.length)
  let ready := setLocal captured "best" (number 0)
  have capture : BlockContinues program env [sourceCode[1]'(by decide)] caller captured
      (built ++ [.list [.ref caller.length]]) globals :=
    BlockContinues.assign (Evaluates.list (.cons generated .nil))
  have readyMax : ready "max_sides" = some (number maxSides) := by
    simpa [ready, captured, setLocal] using getMax
  obtain ⟨searched, finalEnv, executed, finalBest⟩ := start_loop maxSides large world ready
    (by simp [ready, captured, setLocal]) readyMax 0 rfl globals
  have model : PolygonalCycleSearch.reference PolygonalFamilies.family maxSides =
      (PolygonalFamilies.family 3).foldl (fun best start => max best (startValue maxSides start)) 0 := by
    rw [PolygonalCycleSearch.reference, if_neg (by omega : ¬ (maxSides : Int) < 3)]
    rfl
  rw [← model] at finalBest
  obtain ⟨buffer, layout⟩ := store.extension
  let extra := buffer ++ [.list [.ref caller.length]] ++ searched
  have finalLayout : (built ++ [.list [.ref caller.length]]) ++ searched = caller ++ extra := by
    rw [layout]
    simp only [extra, List.append_assoc]
  refine ⟨extra, ?_⟩
  rw [← finalLayout]
  apply BlockReturns.function rfl rfl
  change BlockReturns program env sourceCode caller _ _ globals
  apply BlockReturns.branch (flag := false) (value := flag false) (middle := caller)
  · exact Evaluates.compare (av := number maxSides) (bv := number 3) (middle := caller) (afterRight := caller)
      (Evaluates.lookup getMax) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]; omega)
  · rfl
  · apply capture.returns
    apply BlockReturns.assign Evaluates.constant
    exact executed.returns (BlockReturns.return_value (Evaluates.lookup finalBest))

/-- Every signed argument has a finite complete family table and a decreasing remaining-type search. -/
theorem heap_result (maxSides : Int) (caller : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number maxSides] caller
      (number (PolygonalCycleSearch.reference PolygonalFamilies.family maxSides)) (caller ++ extra) globals := by
  by_cases low : maxSides < 3
  · refine ⟨[], ?_⟩
    simp only [PolygonalCycleSearch.reference, if_pos low, List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (flag := true) (value := flag true) (middle := caller)
    · exact Evaluates.compare (av := number maxSides) (bv := number 3) (middle := caller) (afterRight := caller)
        (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag, low])
    · rfl
    · exact BlockReturns.return_value Evaluates.constant
  · lift maxSides to Nat using (by omega : 0 ≤ maxSides)
    exact positive_result maxSides (by omega) caller globals

theorem «Returns» (maxSides : Int) :
    (HeapCalls.scalarFunction program "naive" [.int maxSides]).Returns := by
  obtain ⟨extra, returned⟩ := heap_result maxSides []
  exact returned.scalar_returns (values := [.int maxSides])

theorem «Supported» (maxSides : Int) :
    (HeapCalls.scalarFunction program "naive" [.int maxSides]).Supported := («Returns» maxSides).supported

end data.«project-euler-statements».data.py.project_euler_statements.p61.naive

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.naive_default
open FormalSW.PyAst HeapCalls ProjectEulerSolutions

theorem heap_result (caller : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue P61Ast.module "naive_default" [] caller
      (.scalar (.int (PolygonalCycleSearch.reference PolygonalFamilies.family 8))) (caller ++ extra) globals := by
  obtain ⟨extra, returned⟩ := naive.heap_result 8 caller globals
  have defaulted := returned.with_defaults (supplied := []) rfl rfl rfl
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call .nil defaulted

theorem «Returns» : (HeapCalls.scalarFunction P61Ast.module "naive_default" []).Returns := by
  obtain ⟨extra, returned⟩ := heap_result []
  exact returned.scalar_returns

end data.«project-euler-statements».data.py.project_euler_statements.p61.naive_default
