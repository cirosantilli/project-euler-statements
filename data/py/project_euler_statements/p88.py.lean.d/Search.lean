import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Loop

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.dfs
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

abbrev parameters : List Arg := ((findFunctionIn program.body "dfs").getD ([], [])).1
def arguments (maxSize limit start : Nat) (before : List Nat) (address : Nat) : List Mutable.Value :=
  [number start, number before.prod, number before.sum, number before.length, number maxSize, number limit, .ref address]
def initialEnv (maxSize limit start : Nat) (before : List Nat) (address : Nat) : HeapCalls.Env :=
  functionEnv parameters dfsCode (arguments maxSize limit start before address) []

/-- Complete source termination and table contents for every reachable factor state. -/
theorem result (maxSize limit start : Nat) (before : List Nat) (valid : Admissible before)
    (lower : 2 ≤ start) (base : Mutable.Heap) (best : List Nat) (length : best.length = maxSize + 1) :
    SearchReturns maxSize limit start before base best := by
  have descendants : Descendants maxSize limit before := by
    intro factor factorBound inside base best length
    have single : Admissible [factor] := by simpa [Admissible] using factorBound
    exact result maxSize limit factor (before ++ [factor])
      (admissible_append before [factor] valid single) factorBound base best length
  have positive := product_positive before valid
  let initial := initialEnv maxSize limit start before base.length
  let measured := setLocal initial "max_f" (number (limit / before.prod))
  let entered := setLocal measured "f" (number start)
  have divisionValue (a b : Nat) (positive : 0 < b) :
      Mutable.binary .floorDiv (number a) (number b) (working base best) =
        some (.ok (number (a / b)), working base best) := by
    simp [Mutable.binary, scalarBinary, number, Int.natCast_ediv,
      Nat.ne_of_gt positive, positive]
  have division : BlockContinues program initial [dfsCode[0]'(by decide)] (working base best)
      measured (working base best) := by
    apply BlockContinues.assign
    apply Evaluates.binary (av := number limit) (bv := number before.prod)
      (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    exact divisionValue limit before.prod (by omega)
  have initialized : BlockContinues program measured [dfsCode[1]'(by decide)] (working base best)
      entered (working base best) := BlockContinues.assign (Evaluates.lookup rfl)
  have ready : Locals entered maxSize limit before base.length := by constructor <;> rfl
  obtain ⟨finalEnv, executed, finalReady⟩ := loop maxSize limit before valid start lower descendants
    base best length entered ready (by simp [entered, setLocal])
  apply BlockReturns.function rfl rfl
  apply division.returns
  apply initialized.returns
  apply executed.returns
  exact BlockReturns.return_value (Evaluates.lookup finalReady.table)
termination_by limit + 1 - before.prod
decreasing_by
  simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  exact descent limit before.prod factor (product_positive before valid) factorBound inside

/-- The reference DFS fills exactly the proved minima table from its source initialization. -/
theorem root (maxSize : Nat) (base : Mutable.Heap) :
    ReturnsValue program "dfs" [number 2, number 1, number 0, number 0,
      number maxSize, number (2 * maxSize), .ref base.length]
      (working base (List.replicate (maxSize + 1) (2 * maxSize + 1))) (.ref base.length)
      (working base (table maxSize)) := by
  exact result maxSize (2 * maxSize) 2 [] (by simp [Admissible]) (by omega) base
    (List.replicate (maxSize + 1) (2 * maxSize + 1)) (by simp)

end data.«project-euler-statements».data.py.project_euler_statements.p88.dfs
