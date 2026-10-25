import data.«project-euler-statements».data.py.project_euler_statements.«p32.search.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32
open FormalSW.PyAst ProjectEulerSolutions.PandigitalProductSearch

theorem naive.«Returns» (width : Int) :
    (SetCalls.call P32Ast.module "naive" [.scalar (.int width)] []).Returns := by
  intro choices
  obtain ⟨heap, returned⟩ := naive.result_int width []
  exact ⟨.scalar (.int (answer width.toNat)), [], heap, 0, returned.finishes choices⟩

theorem naive.«Supported» (width : Int) :
    (SetCalls.call P32Ast.module "naive" [.scalar (.int width)] []).Supported := by
  intro choices
  exact (naive.«Returns» width choices).supported

end data.«project-euler-statements».data.py.project_euler_statements.p32
