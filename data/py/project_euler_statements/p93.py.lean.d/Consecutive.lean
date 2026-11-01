import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Enumeration
import ProjectEulerSolutions.Lib.PositiveRun
import lang.py.FormalSW.MembershipCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_count
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.PositiveRun
set_option Elab.async false

abbrev program := P93Ast.module
abbrev body : List Stmt := [.augAssign (.name "n") .add (.constant (.int 1))]
abbrev guard : Expr := .membership (.name "n") (.name "xs") false
abbrev tailCode : List Stmt :=
  [.whileDo guard body [], .return (.binOp (.name "n") .sub (.constant (.int 1)))]

theorem loop (xs : List Int) (heap : Mutable.Heap) (address n : Nat)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (input : heap[address]? = some (.list (xs.map Heap.number)))
    (positiveN : 0 < n) (within : n ≤ firstMissing xs)
    (getXs : env "xs" = some (.ref address)) (getN : env "n" = some (Heap.number n)) :
    BlockReturns program env tailCode heap (Heap.number (length xs)) heap globals := by
  induction measure : firstMissing xs - n using Nat.strong_induction_on generalizing n env with
  | h remaining ih =>
    have membership : Evaluates program env guard heap
        (.scalar (.bool (decide ((n : Int) ∈ xs)))) heap globals :=
      Evaluates.membership (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getXs) .nil))
        (membership_list_ints heap address n xs input false)
    by_cases finished : n = firstMissing xs
    · have absent : (n : Int) ∉ xs := finished ▸ missing xs
      apply BlockReturns.while_loop (middle := heap) (flag := false) membership
        (by simp [absent, Mutable.truth, scalarTruth])
      apply BlockReturns.return_value
      apply Evaluates.binary (Evaluates.lookup getN) Evaluates.constant
      have count : (n : Int) - 1 = (length xs : Int) := by
        have := firstMissing_eq_length xs
        omega
      simp [Mutable.binary, scalarBinary, count]
    · have earlier : n < firstMissing xs := by omega
      have present := before xs n positiveN earlier
      let next := setLocal env "n" (Heap.number (n + 1))
      have continued := ih (firstMissing xs - (n + 1)) (by omega) (n + 1) next
        (by omega) (by omega) (by simpa [next, setLocal] using getXs) (by simp [next, setLocal]) rfl
      have advanced := BlockReturns.augAssign getN (Evaluates.constant (value := .int 1))
        (show inplace .add (Heap.number n) (Heap.number 1) heap =
          some (.ok (Heap.number (n + 1)), heap) by
            simp [inplace, Mutable.binary, scalarBinary]) continued
      apply BlockReturns.while_loop (middle := heap) (flag := true) membership
        (by simp [present, Mutable.truth, scalarTruth])
      simpa only [tailCode, body, Calls.loopContinuation, Calls.loopControl,
        Calls.loopControlStmt, Bool.false_or, Bool.false_eq_true, if_false] using advanced

/-- The source scans to the least missing positive integer without a runtime cutoff. -/
theorem result (xs : List Int) (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals)
    (input : heap[address]? = some (.list (xs.map Heap.number))) :
    ReturnsValue program "consecutive_count" [.ref address] heap (Heap.number (length xs)) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply loop xs heap address 1 _ globals input (by decide) (by have := positive xs; omega)
  · cases globals <;> rfl
  · rfl

end data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_count
