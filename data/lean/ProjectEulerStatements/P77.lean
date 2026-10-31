import ProjectEulerStatements.Lib.PrimePartitions

/-! The least prime-partition count above a signed threshold, without a search cutoff. -/
namespace ProjectEulerStatements.P77
set_option Elab.async false

def primesUpTo (n : Nat) : List Nat := PrimePartitions.primesUpTo n

def countPrimeSums (n : Nat) : Nat := PrimePartitions.count n

def firstOver (target : Int) : Nat := PrimePartitions.answer target

theorem firstOver_spec (target : Int) :
    2 ≤ firstOver target ∧ target < (countPrimeSums (firstOver target) : Int) :=
  PrimePartitions.answer_spec target

theorem firstOver_le (target : Int) (n : Nat) (lower : 2 ≤ n)
    (exceeds : target < (countPrimeSums n : Int)) : firstOver target ≤ n :=
  PrimePartitions.answer_le target n ⟨lower, exceeds⟩

def naive (target : Int) : Int := firstOver target

end ProjectEulerStatements.P77
