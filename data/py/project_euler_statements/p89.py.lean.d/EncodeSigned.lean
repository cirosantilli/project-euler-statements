import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».EncodeLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false
variable {globals : Mutable.Globals}

/-- Negative inputs skip the loop; nonnegative inputs follow exact quotient/remainder subtraction. -/
theorem repeat_signed (denomination : Nat) (positive : 0 < denomination)
    (token : List Mutable.Value) (tokenAddress : Nat) (base : Mutable.Heap)
    (found : base[tokenAddress]? = some (.list token)) (n : Int) (output : List Mutable.Value)
    (env : HeapCalls.Env) (getN : env "n" = some (.scalar (.int n)))
    (getV : env "v" = some (number denomination)) (getToken : env "cs" = some (.ref tokenAddress))
    (getOut : env "out" = some (.ref base.length)) :
    ∃ finalEnv remainder,
      BlockContinues (globals := globals) program env loopCode (HeapCollection.working base output []) finalEnv
        (HeapCollection.working base (output ++ copies token (n.toNat / denomination)) []) ∧
      finalEnv "n" = some (.scalar (.int remainder)) ∧
      remainder.toNat = n.toNat % denomination ∧
      finalEnv "out" = some (.ref base.length) ∧
      ∀ name, name ≠ "n" → name ≠ "out" → finalEnv name = env name := by
  by_cases negative : n < 0
  · have zero : n.toNat = 0 := by omega
    refine ⟨env, n, ?_, getN, by simp [zero], getOut, fun _ _ _ => rfl⟩
    simp only [zero, Nat.zero_div, copies_zero, List.append_nil]
    apply BlockContinues.while_loop (flag := false) (value := .scalar (.bool false))
      (middle := HeapCollection.working base output [])
    · apply Evaluates.compare (Evaluates.lookup getN) (Evaluates.lookup getV)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, show ¬ n ≥ (denomination : Int) by omega]
    · rfl
    · exact .nil
  · lift n to Nat using (by omega : 0 ≤ n)
    obtain ⟨finalEnv, ran, ready, stable⟩ := repeat_token (globals := globals) denomination positive token tokenAddress base found n output env
      ⟨getN, getV, getToken, getOut⟩
    exact ⟨finalEnv, (n % denomination : Nat), ran, ready.remaining, by simp only [Int.toNat_natCast], ready.output, stable⟩

end data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
