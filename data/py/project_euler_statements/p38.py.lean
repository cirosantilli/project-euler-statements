import data.«project-euler-statements».data.py.project_euler_statements.«p38.search.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p38.naive
open FormalSW.PyAst

theorem «Returns» (width : Int) : (HeapCalls.scalarFunction P38Ast.module "naive" [.int width]).Returns := by
  by_cases negative : width < 0
  · exact (empty (globals := []) width (by omega) []).scalar_returns (values := [.int width])
  · lift width to Nat using (by omega : 0 ≤ width)
    obtain ⟨_, returned⟩ := result (globals := []) width []
    exact returned.scalar_returns (values := [.int width])

theorem «Supported» (width : Int) : (HeapCalls.scalarFunction P38Ast.module "naive" [.int width]).Supported :=
  («Returns» width).supported

end data.«project-euler-statements».data.py.project_euler_statements.p38.naive
