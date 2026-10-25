import data.«project-euler-statements».data.py.project_euler_statements.«p51.families.source»
import ProjectEulerSolutions.Lib.PrimeReplacementMinimum
import lang.py.FormalSW.LoopProgress

/-! The unbounded reference search terminates exactly when a qualifying family exists. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p51.naive
open FormalSW.PyAst FormalSW.PyAst.HeapCalls ProjectEulerSolutions.PrimeReplacementMinimum
set_option Elab.async false
private abbrev program := P51Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def body : List Stmt :=
  [.ifThen (.call (.name "has_prime_family") [.name "k", .name "n"]) [.return (.name "n")] [],
    .augAssign (.name "n") .add (.constant (.int 1))]

private theorem loop (k : Int) (success : Success k) (first : Nat) (within : first ≤ answer k success)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getK : env "k" = some (number k))
    (getN : env "n" = some (number first)) :
    ∃ extra, BlockReturns program env [.whileDo (.constant (.bool true)) body []] heap
      (number (answer k success)) (heap ++ extra) := by
  obtain ⟨allocated, returned⟩ := has_prime_family.result k first heap
  have tested : Evaluates program env (.call (.name "has_prime_family") [.name "k", .name "n"]) heap
      (flag (accepts k first)) (heap ++ allocated) :=
    Evaluates.call (.cons (Evaluates.lookup getK) (.cons (Evaluates.lookup getN) .nil)) returned
  by_cases accepted : accepts k first = true
  · have same : first = answer k success := by
      have least := answer_minimal k success first accepted
      omega
    refine ⟨allocated, ?_⟩
    apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
    apply BlockReturns.branch (flag := true) (by simpa only [accepted] using tested) rfl
    exact BlockReturns.return_value (Evaluates.lookup (by simpa only [same] using getN))
  · have earlier : first < answer k success := by
      have winner := answer_accepted k success
      by_contra late
      have same : first = answer k success := by omega
      exact accepted (same ▸ winner)
    have rejected : accepts k first = false := by cases value : accepts k first <;> simp_all
    let next := setLocal env "n" (number (first + 1 : Nat))
    obtain ⟨extra, rest⟩ := loop k success (first + 1) (by omega) (heap ++ allocated) next
      (by simpa [next, setLocal] using getK) (by simp [next, setLocal])
    refine ⟨allocated ++ extra, ?_⟩
    apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
    apply BlockReturns.branch (flag := false) (by simpa only [rejected] using tested) rfl
    apply BlockReturns.augAssign (value := number (first + 1 : Nat)) (middle := heap ++ allocated)
      (afterOperation := heap ++ allocated) getN Evaluates.constant
    · simp [inplace, Mutable.binary, scalarBinary]
    · simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, List.append_assoc] using rest
termination_by answer k success - first
decreasing_by omega

/-- Any genuine witness makes the source enumerate to the least qualifying prime. -/
theorem result (k : Int) (success : Success k) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number k] heap (number (answer k success)) (heap ++ extra) := by
  let env := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number k] []
  obtain ⟨extra, scanned⟩ := loop k success 0 (Nat.zero_le _) heap (setLocal env "n" (number 0))
    (by simp [setLocal]; rfl) (by simp [setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  exact scanned

/-- Without a matching family, every iteration reaches the next supported boundary. -/
theorem diverges (k : Int) (absent : ¬ Success k) : (HeapCalls.scalarFunction program "naive" [.int k]).Diverges := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := functionEnv args sourceBody [number k] []
  let ready := setLocal entry "n" (number 0)
  let invariant : HeapCalls.Env → Mutable.Heap → Prop := fun env _ =>
    ∃ n : Nat, env "k" = some (number k) ∧ env "n" = some (number n)
  apply scalar_while_diverges program "naive" [.int k] args sourceBody
    [.assign [.name "n"] (.constant (.int 0))] body [number k] rfl rfl rfl rfl invariant ready []
  · exact BlockContinues.assign Evaluates.constant
  · exact ⟨0, by simp [ready, entry, setLocal]; rfl, by simp [ready, setLocal]⟩
  · intro env heap current
    obtain ⟨n, getK, getN⟩ := current
    obtain ⟨extra, returned⟩ := has_prime_family.result k n heap
    have tested : Evaluates program env (.call (.name "has_prime_family") [.name "k", .name "n"])
        heap (flag false) (heap ++ extra) := by
      have rejected : ProjectEulerStatements.P51.hasPrimeFamily k.toNat n = false := no_success k absent n
      simpa only [rejected] using
        (Evaluates.call (.cons (Evaluates.lookup getK) (.cons (Evaluates.lookup getN) .nil)) returned)
    let next := setLocal env "n" (number (n + 1 : Nat))
    have skipped : BlockContinues program env [body[0]'(by decide)] heap env (heap ++ extra) :=
      BlockContinues.branch tested rfl BlockContinues.nil
    have incremented : BlockContinues program env [body[1]'(by decide)] (heap ++ extra) next (heap ++ extra) := by
      apply BlockContinues.augAssign (left := number n) (right := number 1) getN Evaluates.constant
      simp [inplace, Mutable.binary, scalarBinary, number]
    exact ⟨next, heap ++ extra, skipped.append incremented, n + 1,
      by simpa [next, setLocal] using getK, by simp [next, setLocal]⟩

end data.«project-euler-statements».data.py.project_euler_statements.p51.naive
