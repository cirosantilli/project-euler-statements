import data.«project-euler-statements».data.py.project_euler_statements.«p92.py.lean.d».Digits
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.DigitSquareReachability
import lang.py.FormalSW.MembershipCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p92.ends_at_89
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.DigitSquareChains
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

abbrev endpoints : Mutable.Object := .tuple [number 1, number 89]
abbrev endpointTest : Expr := .membership (.name "x") (.tuple [.constant (.int 1), .constant (.int 89)]) true
abbrev seenTest : Expr := .membership (.name "x") (.name "seen") true
abbrev condition : Expr := .boolOp .and [endpointTest, seenTest]
def active (n : Nat) (seen : List Nat) : Bool := !decide (n = 1 ∨ n = 89) && !decide (n ∈ seen)

abbrev state (caller : Mutable.Heap) (seen : List Nat) (garbage : Mutable.Heap) :=
  working caller (seen.map number) garbage

theorem endpoint_test (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getX : env "x" = some (number n)) :
    Evaluates program env endpointTest heap (.scalar (.bool (!decide (n = 1 ∨ n = 89))))
      (heap ++ [endpoints]) globals := by
  apply Evaluates.membership
    (.cons (Evaluates.lookup getX) (.cons (Evaluates.tuple (.cons Evaluates.constant (.cons Evaluates.constant .nil)) (by simp)) .nil))
  have tested := membership_tuple_ints (heap ++ [endpoints]) heap.length n [1, 89] (by simp) true
  have castTarget : (n : Int) = 89 ↔ n = 89 := by omega
  simpa [List.mem_cons, number, castTarget] using tested

theorem seen_test (n : Nat) (seen : List Nat) (caller garbage : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getX : env "x" = some (number n))
    (getSeen : env "seen" = some (.ref caller.length)) :
    Evaluates program env seenTest (state caller seen garbage)
      (.scalar (.bool (!decide (n ∈ seen)))) (state caller seen garbage) globals := by
  apply Evaluates.membership (.cons (Evaluates.lookup getX) (.cons (Evaluates.lookup getSeen) .nil))
  have tested := membership_list_ints (state caller seen garbage) caller.length n
    (seen.map (fun n : Nat => (n : Int))) (by simp [state, number, List.map_map]) true
  simpa [List.mem_map] using tested

/-- The endpoint tuple is allocated on every test; the seen-list membership is short-circuited. -/
theorem guard_result (n : Nat) (seen : List Nat) (caller garbage : Mutable.Heap) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getX : env "x" = some (number n))
    (getSeen : env "seen" = some (.ref caller.length)) :
    Evaluates program env condition (state caller seen garbage)
      (.scalar (.bool (active n seen))) (state caller seen (garbage ++ [endpoints])) globals := by
  have first := endpoint_test n (state caller seen garbage) env globals getX
  rw [ProjectEulerSolutions.HeapCollection.append] at first
  have second := seen_test n seen caller (garbage ++ [endpoints]) env globals getX getSeen
  cases endpoint : decide (n = 1 ∨ n = 89) with
  | true =>
      simp only [endpoint, Bool.not_true] at first
      simpa only [condition, active, endpoint, Bool.not_true, Bool.false_and] using
        (Evaluates.boolean_stop (op := .and) (rest := [seenTest]) first rfl rfl)
  | false =>
      simp only [endpoint, Bool.not_false] at first
      simpa only [condition, active, endpoint, Bool.not_false, Bool.true_and] using
        (Evaluates.boolean_next (op := .and) first rfl rfl (Evaluates.boolean_last second rfl))

end data.«project-euler-statements».data.py.project_euler_statements.p92.ends_at_89
