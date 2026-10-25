import data.«project-euler-statements».data.py.project_euler_statements.«p73.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p73
open FormalSW.PyAst ProjectEulerStatements.FractionIntervalCount
set_option Elab.async false

abbrev denominatorCondition (module : Module) (name : String) (value : Int) : Prop :=
  Calls.Condition module (fun key => if key = name then some (.int value) else none)
    (.compare (.name name) [(.gt, .constant (.int 0))])

theorem denominator_positive (module : Module) (name : String) (value : Int)
    (condition : denominatorCondition module name value) : 0 < value := by
  simpa [evalCmpOp] using
    Calls.Evaluates.condition_int_compare condition (by simp)

theorem count_between.«Returns» (d lowerNum lowerDen upperNum upperDen : Int) :
    (Calls.function program "count_between"
      (values d ⟨lowerNum, lowerDen, upperNum, upperDen⟩)).Returns :=
  (count_between.result d ⟨lowerNum, lowerDen, upperNum, upperDen⟩).returns

theorem count_between.«Supported» (d lowerNum lowerDen upperNum upperDen : Int) :
    (Calls.function program "count_between"
      (values d ⟨lowerNum, lowerDen, upperNum, upperDen⟩)).Supported :=
  (count_between.«Returns» d lowerNum lowerDen upperNum upperDen).supported

namespace naive

theorem «Returns» (limit lowerNum lowerDen upperNum upperDen : Int)
    (_lower : denominatorCondition program "lower_den" lowerDen)
    (_upper : denominatorCondition program "upper_den" upperDen) :
    (Calls.function program "naive"
      (values limit ⟨lowerNum, lowerDen, upperNum, upperDen⟩)).Returns :=
  (result limit ⟨lowerNum, lowerDen, upperNum, upperDen⟩).returns

theorem «Supported» (limit lowerNum lowerDen upperNum upperDen : Int)
    (lower : denominatorCondition program "lower_den" lowerDen)
    (upper : denominatorCondition program "upper_den" upperDen) :
    (Calls.function program "naive"
      (values limit ⟨lowerNum, lowerDen, upperNum, upperDen⟩)).Supported :=
  («Returns» limit lowerNum lowerDen upperNum upperDen lower upper).supported

theorem defaults_returns (limit : Int) (p : Bounds) (supplied : List Constant)
    (omitted : naiveArgs.length ≠ supplied.length)
    (completed : Calls.completeArguments naiveArgs supplied = some (values limit p)) :
    (Calls.function program "naive" supplied).Returns :=
  (default_result limit p supplied omitted completed).returns

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p73
