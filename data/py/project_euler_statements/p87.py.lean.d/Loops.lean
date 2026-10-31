import data.«project-euler-statements».data.py.project_euler_statements.«p87.py.lean.d».Collector

namespace data.«project-euler-statements».data.py.project_euler_statements.p87.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PrimePowerTriples
set_option Elab.async false

abbrev innerBody : List Stmt :=
  [.assign [.name "s"] sumExpression,
   .ifThen (.compare (.name "s") [(.lt, .name "limit")])
     [.expr (.call (.attribute (.name "sums") "append") [.name "s"])] []]
abbrev middleBody : List Stmt := [.forIn (.name "r") (.name "ps") innerBody []]
abbrev outerBody : List Stmt := [.forIn (.name "q") (.name "ps") middleBody []]

structure Locals (env : HeapCalls.Env) (limit primeAddress sumAddress : Nat) : Prop where
  bound : env "limit" = some (number limit)
  primes : env "ps" = some (.ref primeAddress)
  sums : env "sums" = some (.ref sumAddress)

theorem Locals.set_other {env : HeapCalls.Env} {limit primeAddress sumAddress : Nat}
    (ready : Locals env limit primeAddress sumAddress) (name : String) (value : Mutable.Value)
    (notLimit : name ≠ "limit") (notPs : name ≠ "ps") (notSums : name ≠ "sums") :
    Locals (setLocal env name value) limit primeAddress sumAddress := by
  rcases ready with ⟨hl, hp, hs⟩
  constructor <;> simp_all [setLocal, Ne.symm]

def emitted (limit p q r : Nat) : List Nat :=
  if p ^ 2 + q ^ 3 + r ^ 4 < limit then [p ^ 2 + q ^ 3 + r ^ 4] else []

theorem emitted_row (limit p q : Nat) (items : List Nat) :
    items.flatMap (emitted limit p q) =
      (items.map (fun r => p ^ 2 + q ^ 3 + r ^ 4)).filter (fun value => decide (value < limit)) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      by_cases inside : p ^ 2 + q ^ 3 + head ^ 4 < limit <;> simp [emitted, inside, ih]

theorem iteration (limit p q r : Nat) (base : Mutable.Heap) (address : Nat) (sums : List Nat)
    (env : HeapCalls.Env) (ready : Locals env limit address base.length)
    (getP : env "p" = some (number p)) (getQ : env "q" = some (number q))
    (getR : env "r" = some (number r)) :
    ∃ finalEnv, BlockContinues program env innerBody (working base sums) finalEnv
      (working base (sums ++ emitted limit p q r)) ∧ Locals finalEnv limit address base.length ∧
      finalEnv "p" = some (number p) ∧ finalEnv "q" = some (number q) := by
  let value := p ^ 2 + q ^ 3 + r ^ 4
  let measured := setLocal env "s" (number value)
  have measuredReady := ready.set_other "s" (number value) (by decide) (by decide) (by decide)
  refine ⟨measured, ?_, measuredReady, by simpa [measured, setLocal] using getP,
    by simpa [measured, setLocal] using getQ⟩
  have assigned : BlockContinues program env [.assign [.name "s"] sumExpression]
      (working base sums) measured (working base sums) :=
    BlockContinues.assign (sum_evaluate p q r (working base sums) env getP getQ getR)
  have tested : Evaluates program measured (.compare (.name "s") [(.lt, .name "limit")])
      (working base sums) (flag (decide (value < limit))) (working base sums) := by
    apply Evaluates.compare (middle := working base sums) (afterRight := working base sums)
      (Evaluates.lookup (show measured "s" = some (number value) by simp [measured, setLocal]))
      (Evaluates.lookup measuredReady.bound)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  apply assigned.append
  by_cases inside : value < limit
  · apply BlockContinues.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, inside])
    have appended := Evaluates.append (module := program) (globals := []) (Evaluates.lookup measuredReady.sums) (working_found base sums)
      (Evaluates.lookup (show measured "s" = some (number value) by simp [measured, setLocal])) (working_found base sums)
    apply BlockContinues.discard
    dsimp [value] at inside
    simpa [emitted, value, inside, natValues, List.map_append, working, List.set_append_right] using appended
  · apply BlockContinues.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, inside])
    dsimp [value] at inside
    simpa [emitted, inside] using
      (BlockContinues.nil (module := program) (globals := []) (env := measured) (heap := working base sums))

theorem inner_loop (limit p q : Nat) (items : List Nat) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (natValues items))) (sums : List Nat)
    (env : HeapCalls.Env) (ready : Locals env limit address base.length)
    (getP : env "p" = some (number p)) (getQ : env "q" = some (number q)) :
    ∃ finalEnv, BlockContinues program env middleBody (working base sums) finalEnv
      (working base (sums ++ items.flatMap (emitted limit p q))) ∧
      Locals finalEnv limit address base.length ∧ finalEnv "p" = some (number p) ∧
      finalEnv "q" = some (number q) := by
  apply collect_for "r" innerBody rfl items base address found (emitted limit p q)
    (fun current => Locals current limit address base.length ∧
      current "p" = some (number p) ∧ current "q" = some (number q))
  · rintro current ⟨locals, hp, hq⟩ r
    exact ⟨locals.set_other "r" (number r) (by decide) (by decide) (by decide),
      by simpa [setLocal] using hp, by simpa [setLocal] using hq⟩
  · rintro r before current ⟨locals, hp, hq⟩ hr
    exact iteration limit p q r base address before current locals hp hq hr
  · exact ⟨ready, getP, getQ⟩
  · exact ready.primes

theorem middle_loop (limit p : Nat) (items : List Nat) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (natValues items))) (sums : List Nat)
    (env : HeapCalls.Env) (ready : Locals env limit address base.length)
    (getP : env "p" = some (number p)) :
    ∃ finalEnv, BlockContinues program env outerBody (working base sums) finalEnv
      (working base (sums ++ items.flatMap (fun q => items.flatMap (emitted limit p q)))) ∧
      Locals finalEnv limit address base.length ∧ finalEnv "p" = some (number p) := by
  apply collect_for "q" middleBody rfl items base address found
    (fun q => items.flatMap (emitted limit p q))
    (fun current => Locals current limit address base.length ∧ current "p" = some (number p))
  · rintro current ⟨locals, hp⟩ q
    exact ⟨locals.set_other "q" (number q) (by decide) (by decide) (by decide), by simpa [setLocal] using hp⟩
  · rintro q before current ⟨locals, hp⟩ hq
    obtain ⟨finalEnv, executed, finalReady, finalP, _⟩ := inner_loop limit p q items base address found before current locals hp hq
    exact ⟨finalEnv, executed, finalReady, finalP⟩
  · exact ⟨ready, getP⟩
  · exact ready.primes

/-- All three source loops append every accepted triple, retaining duplicates until the final set. -/
theorem collect (limit : Nat) (items : List Nat) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (natValues items))) (sums : List Nat)
    (env : HeapCalls.Env) (ready : Locals env limit address base.length) :
    ∃ finalEnv, BlockContinues program env [.forIn (.name "p") (.name "ps") outerBody []]
      (working base sums) finalEnv (working base (sums ++ referenceValues limit items)) ∧
      Locals finalEnv limit address base.length := by
  have executed := collect_for "p" outerBody rfl items base address found
    (fun p => items.flatMap (fun q => items.flatMap (emitted limit p q)))
    (fun current => Locals current limit address base.length)
    (fun current locals p => locals.set_other "p" (number p) (by decide) (by decide) (by decide))
    (fun p before current locals hp => by
      obtain ⟨finalEnv, steps, finalReady, _⟩ := middle_loop limit p items base address found before current locals hp
      exact ⟨finalEnv, steps, finalReady⟩) sums env ready ready.primes
  simpa only [emitted_row, referenceValues] using executed

end data.«project-euler-statements».data.py.project_euler_statements.p87.naive
