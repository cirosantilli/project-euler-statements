import ProjectEulerStatements.Lib.FractionIntervalCount

set_option linter.style.header false

/-! Exhaustive proper-fraction counts for arbitrary rational interval endpoints. -/
namespace ProjectEulerStatements.P73
open FractionIntervalCount

def naive (limit : Int) (lowerNum : Int := 1) (lowerDen : Int := 3)
    (upperNum : Int := 1) (upperDen : Int := 2) : Nat :=
  result ⟨lowerNum, lowerDen, upperNum, upperDen⟩ limit

end ProjectEulerStatements.P73
