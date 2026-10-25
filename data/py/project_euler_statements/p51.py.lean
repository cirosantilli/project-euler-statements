import data.«project-euler-statements».data.py.project_euler_statements.«p51.search.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p51.naive
open FormalSW.PyAst ProjectEulerSolutions.PrimeReplacementMinimum

theorem returns_iff (k : Int) : (HeapCalls.scalarFunction P51Ast.module "naive" [.int k]).Returns ↔ Success k := by
  classical
  constructor
  · rintro ⟨value, returned⟩
    by_contra absent
    exact Execution.diverges_not_halts (diverges k absent) ⟨.ok value, returned⟩
  · intro success
    obtain ⟨_, returned⟩ := result k success []
    exact returned.scalar_returns (values := [.int k])

theorem returns_le_eight (k : Int) (small : k ≤ 8) :
    (HeapCalls.scalarFunction P51Ast.module "naive" [.int k]).Returns := (returns_iff k).mpr (small_success k small)

theorem «Supported» (k : Int) : (HeapCalls.scalarFunction P51Ast.module "naive" [.int k]).Supported := by
  classical
  by_cases success : Success k
  · exact ((returns_iff k).mpr success).supported
  · exact (diverges k success).supported

end data.«project-euler-statements».data.py.project_euler_statements.p51.naive
