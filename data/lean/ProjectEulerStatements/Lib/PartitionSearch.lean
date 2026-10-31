import ProjectEulerStatements.P76
import Mathlib.Data.Nat.Find

/-! The least positive divisible partition index, conditional only on its existence. -/
namespace ProjectEulerStatements.PartitionSearch
set_option Elab.async false

def Accepted (modulus : Int) (n : Nat) : Prop :=
  0 < n ∧ (P76.countWays n n : Int) % modulus = 0

instance (modulus : Int) (n : Nat) : Decidable (Accepted modulus n) := inferInstanceAs
  (Decidable (0 < n ∧ (P76.countWays n n : Int) % modulus = 0))

def Success (modulus : Int) : Prop := ∃ n, Accepted modulus n

def answer (modulus : Int) (success : Success modulus) : Nat := Nat.find success

theorem answer_spec (modulus : Int) (success : Success modulus) :
    Accepted modulus (answer modulus success) := Nat.find_spec success

theorem answer_positive (modulus : Int) (success : Success modulus) :
    0 < answer modulus success := (answer_spec modulus success).1

theorem before_answer (modulus : Int) (success : Success modulus) (n : Nat)
    (positive : 0 < n) (before : n < answer modulus success) :
    (P76.countWays n n : Int) % modulus ≠ 0 := by
  intro divides
  exact Nat.find_min success before ⟨positive, divides⟩

theorem absent (modulus : Int) (none : ¬ Success modulus) (n : Nat) (positive : 0 < n) :
    (P76.countWays n n : Int) % modulus ≠ 0 := by
  intro divides
  exact none ⟨n, positive, divides⟩

end ProjectEulerStatements.PartitionSearch
