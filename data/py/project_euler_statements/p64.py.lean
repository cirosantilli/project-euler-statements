import data.«project-euler-statements».data.py.project_euler_statements.«p64.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p64.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (limit : Int) : (HeapCalls.scalarFunction P64Ast.module "naive" [.int limit]).Returns := by
  obtain ⟨_, returned⟩ := result limit []
  exact returned.scalar_returns (values := [.int limit])

theorem «Supported» (limit : Int) : (HeapCalls.scalarFunction P64Ast.module "naive" [.int limit]).Supported :=
  («Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p64.naive
