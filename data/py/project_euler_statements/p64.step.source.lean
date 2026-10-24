import data.«project-euler-statements».data.py.project_euler_statements.«p64.dictionary.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p64
open FormalSW.PyAst HeapCalls ProjectEulerStatements.SqrtReducedStates
set_option Elab.async false
private abbrev program := P64Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
variable {globals : Mutable.Globals}

def stepBody : List Stmt :=
  [.assign [.name "m"] (.binOp (.binOp (.name "d") .mult (.name "a")) .sub (.name "m")),
   .assign [.name "d"] (.binOp (.binOp (.name "n") .sub (.binOp (.name "m") .mult (.name "m")))
     .floorDiv (.name "d")),
   .assign [.name "a"] (.binOp (.binOp (.name "a0") .add (.name "m")) .floorDiv (.name "d"))]

def stepEnv (n index : Nat) (env : HeapCalls.Env) : HeapCalls.Env :=
  setLocal (setLocal (setLocal env "m" (number (trajectory n (index + 1)).1))
    "d" (number (trajectory n (index + 1)).2))
    "a" (number (coefficient (Nat.sqrt n) (trajectory n (index + 1))))

theorem step_evaluates (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getRoot : env "a0" = some (number (Nat.sqrt n)))
    (getM : env "m" = some (number (trajectory n index).1))
    (getD : env "d" = some (number (trajectory n index).2))
    (getA : env "a" = some (number (coefficient (Nat.sqrt n) (trajectory n index)))) :
    BlockContinues program env stepBody heap (stepEnv n index env) heap globals := by
  let state := trajectory n index
  let next := trajectory n (index + 1)
  have nextEq : step n (Nat.sqrt n) state = next := trajectory_step n index
  have mStep : state.2 * coefficient (Nat.sqrt n) state - state.1 = next.1 := congrArg Prod.fst nextEq
  have dStep : ((n : Int) - next.1 ^ 2) / state.2 = next.2 := by
    have same := congrArg Prod.snd nextEq
    change ((n : Int) - (state.2 * coefficient (Nat.sqrt n) state - state.1) ^ 2) / state.2 = next.2 at same
    simpa only [mStep] using same
  have currentPositive : 0 < state.2 := trajectory_denominator_positive n index nonsquare
  have nextPositive : 0 < next.2 := trajectory_denominator_positive n (index + 1) nonsquare
  let e1 := setLocal env "m" (number next.1)
  let e2 := setLocal e1 "d" (number next.2)
  have first : BlockContinues program env
      [.assign [.name "m"] (.binOp (.binOp (.name "d") .mult (.name "a")) .sub (.name "m"))] heap e1 heap globals := by
    apply BlockContinues.assign
    exact Evaluates.binary (av := number (state.2 * coefficient (Nat.sqrt n) state)) (bv := number state.1)
      (middle := heap) (afterRight := heap)
      (Evaluates.binary (av := number state.2) (bv := number (coefficient (Nat.sqrt n) state))
        (middle := heap) (afterRight := heap) (Evaluates.lookup getD) (Evaluates.lookup getA)
        (by simp [Mutable.binary, scalarBinary, number]))
      (Evaluates.lookup getM) (by simp [Mutable.binary, scalarBinary, number, mStep])
  have second : BlockContinues program e1
      [.assign [.name "d"] (.binOp (.binOp (.name "n") .sub (.binOp (.name "m") .mult (.name "m")))
        .floorDiv (.name "d"))] heap e2 heap globals := by
    apply BlockContinues.assign
    exact Evaluates.binary (av := number ((n : Int) - next.1 ^ 2)) (bv := number state.2)
      (middle := heap) (afterRight := heap)
      (Evaluates.binary (av := number n) (bv := number (next.1 ^ 2))
        (middle := heap) (afterRight := heap) (Evaluates.lookup (by simpa [e1, setLocal] using getN))
        (Evaluates.binary (av := number next.1) (bv := number next.1)
          (middle := heap) (afterRight := heap)
          (Evaluates.lookup (by simp [e1, setLocal])) (Evaluates.lookup (by simp [e1, setLocal]))
          (by simp [Mutable.binary, scalarBinary, number, pow_two]))
        (by simp [Mutable.binary, scalarBinary, number]))
      (Evaluates.lookup (by simpa [e1, setLocal] using getD))
      (by simp [Mutable.binary, scalarBinary, number, ne_of_gt currentPositive, currentPositive, dStep])
  have third : BlockContinues program e2
      [.assign [.name "a"] (.binOp (.binOp (.name "a0") .add (.name "m")) .floorDiv (.name "d"))]
      heap (stepEnv n index env) heap globals := by
    apply BlockContinues.assign
    exact Evaluates.binary (av := number ((Nat.sqrt n : Int) + next.1)) (bv := number next.2)
      (middle := heap) (afterRight := heap)
      (Evaluates.binary (av := number (Nat.sqrt n)) (bv := number next.1)
        (middle := heap) (afterRight := heap)
        (Evaluates.lookup (by simpa [e2, e1, setLocal] using getRoot))
        (Evaluates.lookup (by simp [e2, e1, setLocal])) (by simp [Mutable.binary, scalarBinary, number]))
      (Evaluates.lookup (by simp [e2, setLocal]))
      (by simp [Mutable.binary, scalarBinary, number, ne_of_gt nextPositive, nextPositive, coefficient, next])
  exact first.append (second.append third)

theorem isqrt_evaluates (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    Evaluates program env (.call (.name "isqrt") [.name "n"]) heap (number (Nat.sqrt n)) heap globals := by
  have root_eq : Math.isqrt n = Nat.sqrt n := Nat.eq_sqrt.mpr (Math.isqrt_spec n)
  apply Evaluates.library_call (.cons (Evaluates.lookup getN) .nil) rfl
  change some (Except.map Mutable.Value.scalar (Math.isqrtCall [.int n]), heap) = _
  simp [Math.isqrtCall, root_eq, show ¬ (n : Int) < 0 by omega, number, Except.map]

theorem is_square.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "is_square" [number n] heap
      (.scalar (.bool (decide (Nat.sqrt n * Nat.sqrt n = n)))) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (isqrt_evaluates n heap _ (by cases globals <;> rfl))
  apply BlockReturns.return_value
  apply Evaluates.compare (av := number ((Nat.sqrt n * Nat.sqrt n : Nat) : Int)) (bv := number n)
    (middle := heap) (afterRight := heap)
  · exact Evaluates.binary (av := number (Nat.sqrt n)) (bv := number (Nat.sqrt n))
      (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) (Evaluates.lookup rfl)
      (by simp [Mutable.binary, scalarBinary, number])
  · exact Evaluates.lookup (by cases globals <;> rfl)
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    norm_cast

end data.«project-euler-statements».data.py.project_euler_statements.p64
