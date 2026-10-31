import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Table

namespace data.«project-euler-statements».data.py.project_euler_statements.p88
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

structure Locals (env : HeapCalls.Env) (maxSize limit : Nat) (before : List Nat) (address : Nat) : Prop where
  product : env "prod" = some (number before.prod)
  summ : env "summ" = some (number before.sum)
  terms : env "terms" = some (number before.length)
  maximum : env "k_max" = some (number maxSize)
  bound : env "limit" = some (number limit)
  table : env "best" = some (.ref address)
  last : env "max_f" = some (number (limit / before.prod))

theorem Locals.measured {env : HeapCalls.Env} {maxSize limit : Nat} {before : List Nat} {address : Nat}
    (ready : Locals env maxSize limit before address) (factor : Nat) :
    Locals (measuredEnv env before factor) maxSize limit before address := by
  rcases ready with ⟨hp, hs, ht, hm, hl, hb, hf⟩
  constructor <;> simp_all [measuredEnv, setLocal]

theorem Locals.factor {env : HeapCalls.Env} {maxSize limit : Nat} {before : List Nat} {address : Nat}
    (ready : Locals env maxSize limit before address) (factor : Nat) :
    Locals (setLocal env "f" (number factor)) maxSize limit before address := by
  rcases ready with ⟨hp, hs, ht, hm, hl, hb, hf⟩
  constructor <;> simp_all [setLocal]

def SearchReturns (maxSize limit start : Nat) (before : List Nat) (base : Mutable.Heap) (best : List Nat) : Prop :=
  ReturnsValue program "dfs" [number start, number before.prod, number before.sum, number before.length,
    number maxSize, number limit, .ref base.length] (working base best) (.ref base.length)
    (working base (accumulate (search maxSize limit start before.prod before.sum before.length) best))

/-- Recursive calls need only the strictly larger products, for every current table. -/
def Descendants (maxSize limit : Nat) (before : List Nat) : Prop :=
  ∀ factor, 2 ≤ factor → before.prod * factor ≤ limit →
    ∀ (base : Mutable.Heap) (best : List Nat), best.length = maxSize + 1 →
      SearchReturns maxSize limit factor (before ++ [factor]) base best

end data.«project-euler-statements».data.py.project_euler_statements.p88
