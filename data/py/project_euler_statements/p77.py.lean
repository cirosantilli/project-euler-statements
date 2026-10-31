import data.«project-euler-statements».data.py.project_euler_statements.«p77.search.source»

/-! The reference terminates at the least answer for every signed threshold. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p77
open FormalSW.PyAst HeapMemoCalls
set_option Elab.async false

theorem naive.scalar_result (target : Int) :
    Finishes (HeapMemoCalls.scalarFunction program "naive" [.int target]).step
      (HeapMemoCalls.scalarFunction program "naive" [.int target]).initial
      (.ok (.int (ProjectEulerStatements.PrimePartitions.answer target))) := by
  have run : ReturnsRel program cacheSpec "naive" [integer target] []
      (fun value after => value = integer (ProjectEulerStatements.PrimePartitions.answer target) ∧
        ∃ extra, after = [] ++ extra) := naive.result target []
  obtain ⟨_, _, finished⟩ := ReturnsRel.scalar_finishes (values := [.int target]) run
  exact finished

theorem naive.«Returns» (target : Int) : (HeapMemoCalls.scalarFunction program "naive" [.int target]).Returns :=
  ⟨_, naive.scalar_result target⟩

theorem naive.«Supported» (target : Int) : (HeapMemoCalls.scalarFunction program "naive" [.int target]).Supported :=
  (naive.«Returns» target).supported

end data.«project-euler-statements».data.py.project_euler_statements.p77
