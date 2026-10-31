import data.«project-euler-statements».data.py.project_euler_statements.«p74.digits.source»
import lang.py.FormalSW.MembershipCalls

/-! The mutable seen-list loop executes exactly the finite first-repeat trace. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p74
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.BoundedOrbit ProjectEulerStatements.DigitFactorialChains
set_option Elab.async false

def chainHeap (base : Mutable.Heap) (seen : List Nat) (garbage : Mutable.Heap) : Mutable.Heap :=
  base ++ (.list (numbers seen) :: garbage)

@[simp] theorem chainHeap_found (base : Mutable.Heap) (seen : List Nat) (garbage : Mutable.Heap) :
    (chainHeap base seen garbage)[base.length]? = some (.list (numbers seen)) := by
  simp [chainHeap]

theorem chainHeap_append (base : Mutable.Heap) (seen : List Nat) (garbage extra : Mutable.Heap) :
    chainHeap base seen garbage ++ extra = chainHeap base seen (garbage ++ extra) := by
  simp [chainHeap, List.append_assoc]

theorem chainHeap_set (base : Mutable.Heap) (seen replacement : List Nat)
    (garbage : Mutable.Heap) :
    (chainHeap base seen garbage).set base.length (.list (numbers replacement)) =
      chainHeap base replacement garbage := by
  simp [chainHeap, List.set_append_right]

abbrev chainTest : Expr := .membership (.name "x") (.name "seen") true
abbrev chainBody : List Stmt :=
  [.expr (.call (.attribute (.name "seen") "append") [.name "x"]),
    .assign [.name "x"] (.call (.name "next_term") [.name "x"])]
abbrev chainCode : List Stmt :=
  [.whileDo chainTest chainBody [], .return (.builtinCall .len [.name "seen"])]

theorem chain_test (current : Nat) (seen : List Nat) (base garbage : Mutable.Heap)
    (env : HeapCalls.Env) (getX : env "x" = some (number current))
    (getSeen : env "seen" = some (.ref base.length)) :
    Evaluates program env chainTest (chainHeap base seen garbage)
      (.scalar (.bool (decide (current ∉ seen)))) (chainHeap base seen garbage) := by
  apply Evaluates.membership (.cons (Evaluates.lookup getX)
    (.cons (Evaluates.lookup getSeen) .nil))
  have found : (chainHeap base seen garbage)[base.length]? =
      some (.list ((seen.map (fun n : Nat => (n : Int))).map
        (fun n => Mutable.Value.scalar (.int n)))) := by
    simpa only [List.map_map, Function.comp_def] using chainHeap_found base seen garbage
  have tested := membership_list_ints (chainHeap base seen garbage) base.length
    (current : Int) (seen.map (fun n : Nat => (n : Int))) found true
  simpa [List.mem_map] using tested

theorem chain_append (current : Nat) (seen : List Nat) (base garbage : Mutable.Heap)
    (env : HeapCalls.Env) (getX : env "x" = some (number current))
    (getSeen : env "seen" = some (.ref base.length)) :
    Evaluates program env (.call (.attribute (.name "seen") "append") [.name "x"])
      (chainHeap base seen garbage) (.scalar .none)
      (chainHeap base (seen ++ [current]) garbage) := by
  have appended := Evaluates.append (globals := []) (module := program)
    (Evaluates.lookup getSeen) (chainHeap_found base seen garbage)
    (Evaluates.lookup getX) (chainHeap_found base seen garbage)
  have values : numbers seen ++ [number current] = numbers (seen ++ [current]) := by
    simp only [numbers, List.map_append, List.map_cons, List.map_nil]
  rw [values, chainHeap_set] at appended
  exact appended

theorem chain_length_result (seen : List Nat) (base garbage : Mutable.Heap)
    (env : HeapCalls.Env) (getSeen : env "seen" = some (.ref base.length)) :
    Evaluates program env (.builtinCall .len [.name "seen"]) (chainHeap base seen garbage)
      (number seen.length) (chainHeap base seen garbage) := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getSeen) .nil)
  simp [primitive, Mutable.length, numbers, number]

/-- Each actual next-term call may allocate; caller objects and the visited list are retained. -/
theorem chain_loop (current : Nat) (seen result : List Nat)
    (trace : Trace ProjectEulerStatements.P74.nextTerm current seen result)
    (base garbage : Mutable.Heap) (env : HeapCalls.Env)
    (getX : env "x" = some (number current))
    (getSeen : env "seen" = some (.ref base.length)) :
    ∃ finalGarbage, BlockReturns program env chainCode (chainHeap base seen garbage)
      (number result.length) (chainHeap base result finalGarbage) := by
  induction trace generalizing garbage env with
  | @done current seen present =>
      refine ⟨garbage, ?_⟩
      apply BlockReturns.while_loop (flag := false)
        (by simpa only [present, not_true_eq_false, decide_false] using
          chain_test current seen base garbage env getX getSeen) rfl
      exact BlockReturns.return_value (chain_length_result seen base garbage env getSeen)
  | @step current seen result fresh rest ih =>
      let advanced := setLocal env "x" (number (ProjectEulerStatements.P74.nextTerm current))
      let extra : Mutable.Heap := [.list (numbers (sourceDigits current))]
      obtain ⟨finalGarbage, completed⟩ := ih (garbage ++ extra) advanced
        (by simp [advanced, setLocal]) (by simpa [advanced, setLocal] using getSeen)
      refine ⟨finalGarbage, ?_⟩
      apply BlockReturns.while_loop (flag := true)
        (by simpa only [fresh, not_false_eq_true, decide_true] using
          chain_test current seen base garbage env getX getSeen) rfl
      simp only [chainBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.cons_append, List.nil_append]
      apply BlockReturns.discard (chain_append current seen base garbage env getX getSeen)
      apply BlockReturns.assign
        (middle := chainHeap base (seen ++ [current]) (garbage ++ extra))
      · have executed := Evaluates.call (.cons (Evaluates.lookup getX) .nil)
          (next_term.result current (chainHeap base (seen ++ [current]) garbage))
        simpa only [chainHeap_append] using executed
      · exact completed

theorem chain_len.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "chain_len" [number n] heap
      (number (ProjectEulerStatements.P74.chainLen n)) (heap ++ extra) := by
  let args := ((findFunctionIn program.body "chain_len").getD ([], [])).1
  let source := ((findFunctionIn program.body "chain_len").getD ([], [])).2
  let entry := functionEnv args source [number n] []
  let ready := assignNames entry ["x", "seen"] [number n, .ref heap.length]
  let pair : Mutable.Object := .tuple [number n, .ref heap.length]
  have getN : entry "n" = some (number n) := rfl
  obtain ⟨garbage, executed⟩ := chain_loop n [] (path n) (path_trace n) heap [pair] ready
    (by rfl) (by rfl)
  refine ⟨.list (numbers (path n)) :: garbage, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := ["x", "seen"])
    (items := [number n, .ref heap.length]) (value := .ref (heap.length + 1))
    (middle := chainHeap heap [] [pair]) (afterUnpack := chainHeap heap [] [pair]) rfl
  · have allocated := Evaluates.tuple (globals := []) (module := program) (env := entry)
      (heap := heap) (.cons (Evaluates.lookup getN) (.cons (Evaluates.list .nil) .nil)) (by simp)
    simpa only [List.length_append, List.length_singleton, List.append_assoc,
      List.cons_append, List.nil_append, chainHeap, pair, numbers, List.map_nil] using allocated
  · simp [Mutable.sequence, chainHeap, pair]
  · rfl
  · exact executed

end data.«project-euler-statements».data.py.project_euler_statements.p74
