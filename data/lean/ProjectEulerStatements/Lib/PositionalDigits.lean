import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring

/-! Positional evaluation for signed digits and bases, with natural-number compatibility. -/
namespace ProjectEulerStatements.PositionalDigits

/-- Evaluate digits in little-endian order. No digit or base restriction is needed. -/
def value (base : Int) : List Int → Int
  | [] => 0
  | digit :: rest => digit + base * value base rest

@[simp] theorem value_nil (base : Int) : value base [] = 0 := rfl

@[simp] theorem value_cons (base digit : Int) (rest : List Int) :
    value base (digit :: rest) = digit + base * value base rest := rfl

/-- The two-accumulator digit loop preserves positional evaluation. -/
theorem step (base digit total multiplier : Int) (rest : List Int) :
    total + multiplier * value base (digit :: rest) =
      (total + digit * multiplier) + (multiplier * base) * value base rest := by
  simp only [value_cons]
  ring

theorem value_naturals (base : Nat) (digits : List Nat) :
    value base (digits.map (fun (n : Nat) => (n : Int))) = Nat.ofDigits base digits := by
  induction digits with
  | nil => simp [Nat.ofDigits]
  | cons digit rest ih => simp [Nat.ofDigits, ih]

end ProjectEulerStatements.PositionalDigits
