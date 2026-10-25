import lang.py.FormalSW.ScalarComparisons
import data.«project-euler-statements».data.py.project_euler_statements.«p71.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p71
open FormalSW.PyAst
set_option Elab.async false

abbrev positiveCondition (module : Module) (num : Int) : Prop :=
  Calls.Condition module (fun key => if key = "num" then some (.int num) else none)
    (.compare (.constant (.int 0)) [(.lt, .name "num")])

abbrev properCondition (module : Module) (num den : Int) : Prop :=
  Calls.Condition module
    (fun key => if key = "num" then some (.int num) else
      if key = "den" then some (.int den) else none)
    (.compare (.name "num") [(.lt, .name "den")])

theorem positive_of_condition (module : Module) (num : Int)
    (condition : positiveCondition module num) : 0 < num := by
  have compared := Calls.Evaluates.condition_compare condition
    Calls.Evaluates.constant (Calls.Evaluates.lookup rfl)
  simpa [evalCmpOp] using compared

theorem proper_of_condition (module : Module) (num den : Int)
    (condition : properCondition module num den) : num < den := by
  have compared := Calls.Evaluates.condition_compare condition
    (Calls.Evaluates.lookup rfl) (Calls.Evaluates.lookup rfl)
  simpa [evalCmpOp] using compared

namespace naive

theorem «Returns» (limit num den : Int)
    (positive : positiveCondition program num) (proper : properCondition program num den) :
    (Calls.function program "naive" [.int limit, .int num, .int den]).Returns :=
  (result limit num den (positive_of_condition program num positive)
    (proper_of_condition program num den proper)).returns

theorem «Supported» (limit num den : Int)
    (positive : positiveCondition program num) (proper : properCondition program num den) :
    (Calls.function program "naive" [.int limit, .int num, .int den]).Supported :=
  («Returns» limit num den positive proper).supported

theorem one_argument_returns (limit : Int) :
    (Calls.function program "naive" [.int limit]).Returns :=
  (one_argument_result limit).returns

theorem two_argument_returns (limit num : Int) (positive : 0 < num) (proper : num < 7) :
    (Calls.function program "naive" [.int limit, .int num]).Returns :=
  (two_argument_result limit num positive proper).returns

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p71
