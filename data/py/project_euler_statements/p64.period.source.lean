import data.«project-euler-statements».data.py.project_euler_statements.«p64.step.source»
import ProjectEulerStatements.P64

namespace data.«project-euler-statements».data.py.project_euler_statements.p64
open FormalSW.PyAst HeapCalls ProjectEulerStatements.SqrtReducedStates ProjectEulerSolutions.SqrtPeriodDictionary
set_option Elab.async false
private abbrev program := P64Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
variable {globals : Mutable.Globals}

def iteration : List Stmt := insertion ++ stepBody
def loop : Stmt := .whileDo condition iteration []
def finalExpr : Expr := .binOp (.builtinCall .len [.name "seen"]) .sub (.subscript (.name "seen") tupleExpr)

/-- The recorded first indices determine the exact cycle length at the first repeated state. -/
theorem loop_result (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (before : index ≤ length n + 1) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (dictionary : Nat) (entries : List (HashDict.Entry Mutable.Value))
    (found : Found heap dictionary entries) (view : Entries n index entries)
    (getN : env "n" = some (number n)) (getRoot : env "a0" = some (number (Nat.sqrt n)))
    (getSeen : env "seen" = some (.ref dictionary))
    (getM : env "m" = some (number (trajectory n index).1))
    (getD : env "d" = some (number (trajectory n index).2))
    (getA : env "a" = some (number (coefficient (Nat.sqrt n) (trajectory n index)))) :
    ∃ finalHeap, BlockReturns program env [loop, .return finalExpr] heap (number (length n)) finalHeap globals := by
  let checked := heap ++ [.tuple (stateValues n index)]
  have checkedFound := found_append found [.tuple (stateValues n index)]
  have tested := membership_evaluates (globals := globals) n index heap env dictionary entries found getSeen getM getD getA
  by_cases fresh : index ≤ length n
  · have missing := entries_missing n index entries view fresh
    let nextEntries := HashDict.insert entries (stateKey n index) (.ref checked.length) (number (index : Int))
    let inserted := (checked ++ [Mutable.Object.tuple (stateValues n index)]).set dictionary (.keyDict nextEntries)
    have stored : BlockContinues program env insertion checked env inserted globals := by
      simpa only [inserted, nextEntries, view.1] using
        insert_evaluates (globals := globals) n index checked env dictionary entries checkedFound getSeen getM getD getA
    have nextFound : Found inserted dictionary nextEntries := Or.inl (by
      apply List.getElem?_set_self
      have inside : dictionary < checked.length := found_inside checkedFound
      simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt inside)
    have nextView : Entries n (index + 1) nextEntries := entries_insert n index entries nonsquare view fresh _
    obtain ⟨finalHeap, rest⟩ := loop_result n (index + 1) nonsquare (by omega) inserted (stepEnv n index env)
      dictionary nextEntries nextFound nextView
      (by simpa [stepEnv, setLocal] using getN) (by simpa [stepEnv, setLocal] using getRoot)
      (by simpa [stepEnv, setLocal] using getSeen)
      (by simp [stepEnv, setLocal]) (by simp [stepEnv, setLocal]) (by simp [stepEnv, setLocal])
    refine ⟨finalHeap, ?_⟩
    apply BlockReturns.while_loop (flag := true) (by simpa only [missing, Option.isSome_none, Bool.not_false] using tested) rfl
    have advanced := step_evaluates (globals := globals) n index nonsquare inserted env getN getRoot getM getD getA
    simpa only [iteration, Calls.loopContinuation, show Calls.loopControl iteration = false from rfl,
      Bool.false_eq_true, if_false, List.append_assoc] using (stored.append advanced).returns rest
  · have done : index = length n + 1 := by omega
    subst index
    have selected := entries_repeat n entries nonsquare view
    refine ⟨checked ++ [.tuple (stateValues n (length n + 1))], ?_⟩
    apply BlockReturns.while_loop (flag := false)
      (by simpa only [selected, Option.isSome_some, Bool.not_true] using tested) rfl
    apply BlockReturns.return_value
    exact Evaluates.binary (av := number entries.length) (bv := number 1)
      (middle := checked) (afterRight := checked ++ [.tuple (stateValues n (length n + 1))])
      (len_evaluates checked env dictionary entries checkedFound getSeen)
      (lookup_evaluates n (length n + 1) checked env dictionary entries checkedFound (number 1) selected getSeen getM getD getA)
      (by simp [Mutable.binary, scalarBinary, number, view.1])
termination_by length n + 1 - index
decreasing_by omega

theorem period_len_full.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ finalHeap, ReturnsValue program "period_len_full" [number n] heap
      (number (ProjectEulerStatements.P64.periodLen n)) finalHeap globals := by
  let args := ((findFunctionIn program.body "period_len_full").getD ([], [])).1
  let body := ((findFunctionIn program.body "period_len_full").getD ([], [])).2
  let original := functionEnv args body [number n] globals
  let rooted := setLocal original "a0" (number (Nat.sqrt n))
  by_cases square : Nat.sqrt n * Nat.sqrt n = n
  · refine ⟨heap, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (isqrt_evaluates n heap _ (by cases globals <;> rfl))
    apply BlockReturns.branch (flag := true)
      (by simpa only [square, decide_true] using
        (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (is_square.result n heap globals))) rfl
    rw [ProjectEulerStatements.P64.periodLen_of_square n square]
    exact BlockReturns.return_value Evaluates.constant
  · let initial := heap ++ [.tuple [number 0, number 1, number (Nat.sqrt n)]]
    let allocated := initial ++ [.dict []]
    let dictionary := initial.length
    let ready := assignNames rooted ["m", "d", "a"] [number 0, number 1, number (Nat.sqrt n)]
    let entered := setLocal ready "seen" (.ref dictionary)
    obtain ⟨finalHeap, executed⟩ := loop_result n 0 square (by omega) allocated entered dictionary []
      (Or.inr ⟨rfl, by simp [allocated, dictionary]⟩) (entries_empty n)
      (by cases globals <;> rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by simp [entered, ready, rooted, assignNames, setLocal, trajectory, coefficient])
    refine ⟨finalHeap, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (isqrt_evaluates n heap _ (by cases globals <;> rfl))
    apply BlockReturns.branch (flag := false)
      (by simpa only [square, decide_false] using
        (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (is_square.result n heap globals))) rfl
    apply BlockReturns.unpack (names := ["m", "d", "a"]) (items := [number 0, number 1, number (Nat.sqrt n)])
      (middle := initial) (afterUnpack := initial) rfl
    · exact Evaluates.tuple (.cons Evaluates.constant (.cons Evaluates.constant
        (.cons (Evaluates.lookup rfl) .nil))) (by simp)
    · simp [Mutable.sequence, initial]
    · rfl
    · apply BlockReturns.assign (value := .ref dictionary) (middle := allocated) (Evaluates.dictionary .nil)
      exact executed

end data.«project-euler-statements».data.py.project_euler_statements.p64
