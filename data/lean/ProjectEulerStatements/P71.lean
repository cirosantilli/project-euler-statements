import ProjectEulerStatements.Lib.FractionSearch

/-! Exhaustive reduced-fraction search with a signed bound and a variable proper target. -/
namespace ProjectEulerStatements.P71

abbrev betterFrac (a b c d : Nat) : Bool := decide (a * d > c * b)
abbrev isReduced (n d : Nat) : Bool := decide (Nat.Coprime n d)

def leftOf (limit : Int) (num den : Nat) : Nat :=
  (FractionSearch.exhaustive num den limit.toNat (0, 1)).1

def naive (limit : Int) (num : Int := 3) (den : Int := 7) : Nat :=
  leftOf limit num.toNat den.toNat

end ProjectEulerStatements.P71
