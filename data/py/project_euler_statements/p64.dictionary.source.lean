import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p64.py.ast»
import ProjectEulerSolutions.Lib.SqrtPeriodDictionary

namespace data.«project-euler-statements».data.py.project_euler_statements.p64
open FormalSW.PyAst HeapCalls ProjectEulerStatements.SqrtReducedStates ProjectEulerSolutions.SqrtPeriodDictionary
set_option Elab.async false
private abbrev program := P64Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
variable {globals : Mutable.Globals}

def Found (heap : Mutable.Heap) (dictionary : Nat) (entries : List (HashDict.Entry Mutable.Value)) : Prop :=
  heap[dictionary]? = some (.keyDict entries) ∨ (entries = [] ∧ heap[dictionary]? = some (.dict []))

theorem found_inside {heap : Mutable.Heap} {dictionary : Nat} {entries : List (HashDict.Entry Mutable.Value)}
    (found : Found heap dictionary entries) : dictionary < heap.length := by
  rcases found with found | ⟨_, found⟩ <;> exact (List.getElem?_eq_some_iff.mp found).1

theorem found_append {heap : Mutable.Heap} {dictionary : Nat} {entries : List (HashDict.Entry Mutable.Value)}
    (found : Found heap dictionary entries) (extra : Mutable.Heap) : Found (heap ++ extra) dictionary entries := by
  have inside := found_inside found
  rcases found with found | ⟨empty, found⟩
  · exact Or.inl (by simpa only [List.getElem?_append_left inside] using found)
  · exact Or.inr ⟨empty, by simpa only [List.getElem?_append_left inside] using found⟩

def tupleExpr : Expr := .tuple [.name "m", .name "d", .name "a"]
def condition : Expr := .membership tupleExpr (.name "seen") true
def insertion : List Stmt :=
  [.assign [.subscript (.name "seen") tupleExpr] (.builtinCall .len [.name "seen"])]

theorem tuple_evaluates (n index : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getM : env "m" = some (number (trajectory n index).1))
    (getD : env "d" = some (number (trajectory n index).2))
    (getA : env "a" = some (number (coefficient (Nat.sqrt n) (trajectory n index)))) :
    Evaluates program env tupleExpr heap (.ref heap.length) (heap ++ [.tuple (stateValues n index)]) globals := by
  exact Evaluates.tuple (.cons (Evaluates.lookup getM)
    (.cons (Evaluates.lookup getD) (.cons (Evaluates.lookup getA) .nil))) (by simp [stateValues, constants])

theorem hash_state (n index : Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.tuple (stateValues n index))) :
    Mutable.hashKey (.ref address) heap = some (.ok (stateKey n index), heap) := by
  exact Mutable.hashKey_tuple_scalars heap address (constants (Nat.sqrt n) (trajectory n index)) found

theorem len_evaluates (heap : Mutable.Heap) (env : HeapCalls.Env) (dictionary : Nat)
    (entries : List (HashDict.Entry Mutable.Value)) (found : Found heap dictionary entries)
    (getSeen : env "seen" = some (.ref dictionary)) :
    Evaluates program env (.builtinCall .len [.name "seen"]) heap (number entries.length) heap globals := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getSeen) .nil)
  rcases found with found | ⟨rfl, found⟩ <;> simp [primitive, Mutable.length, found, number]

/-- Membership allocates a fresh tuple, then looks up its immutable scalar representation. -/
theorem membership_evaluates (n index : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (dictionary : Nat) (entries : List (HashDict.Entry Mutable.Value)) (found : Found heap dictionary entries)
    (getSeen : env "seen" = some (.ref dictionary))
    (getM : env "m" = some (number (trajectory n index).1))
    (getD : env "d" = some (number (trajectory n index).2))
    (getA : env "a" = some (number (coefficient (Nat.sqrt n) (trajectory n index)))) :
    Evaluates program env condition heap (flag (!(HashDict.lookup entries (stateKey n index)).isSome))
      (heap ++ [.tuple (stateValues n index)]) globals := by
  let middle := heap ++ [.tuple (stateValues n index)]
  have appended := found_append found [.tuple (stateValues n index)]
  have hashed := hash_state n index middle heap.length (by simp [middle])
  dsimp only [middle] at hashed
  apply Evaluates.membership
    (.cons (tuple_evaluates n index heap env getM getD getA) (.cons (Evaluates.lookup getSeen) .nil))
  rcases appended with got | ⟨rfl, got⟩ <;>
    simp [HeapCalls.membership, got, hashed, Mutable.promoteDictionary, flag, Except.map]

/-- Assignment evaluates the old size before allocating the key and updating the shared table. -/
theorem insert_evaluates (n index : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (dictionary : Nat) (entries : List (HashDict.Entry Mutable.Value)) (found : Found heap dictionary entries)
    (getSeen : env "seen" = some (.ref dictionary))
    (getM : env "m" = some (number (trajectory n index).1))
    (getD : env "d" = some (number (trajectory n index).2))
    (getA : env "a" = some (number (coefficient (Nat.sqrt n) (trajectory n index)))) :
    BlockContinues program env insertion heap env
      ((heap ++ [Mutable.Object.tuple (stateValues n index)]).set dictionary
        (.keyDict (HashDict.insert entries (stateKey n index) (.ref heap.length) (number entries.length)))) globals := by
  let middle := heap ++ [.tuple (stateValues n index)]
  have appended := found_append found [.tuple (stateValues n index)]
  have hashed := hash_state n index middle heap.length (by simp [middle])
  dsimp only [middle] at hashed
  apply BlockContinues.setItem (by intro a b c impossible; cases impossible)
    (len_evaluates heap env dictionary entries found getSeen)
    (.cons (Evaluates.lookup getSeen) (.cons (tuple_evaluates n index heap env getM getD getA) .nil))
  rcases appended with got | ⟨rfl, got⟩ <;>
    simp [Mutable.setItem, got, hashed, Mutable.promoteDictionary, Except.map]

theorem lookup_evaluates (n index : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (dictionary : Nat) (entries : List (HashDict.Entry Mutable.Value)) (found : Found heap dictionary entries)
    (value : Mutable.Value) (selected : HashDict.lookup entries (stateKey n index) = some value)
    (getSeen : env "seen" = some (.ref dictionary))
    (getM : env "m" = some (number (trajectory n index).1))
    (getD : env "d" = some (number (trajectory n index).2))
    (getA : env "a" = some (number (coefficient (Nat.sqrt n) (trajectory n index)))) :
    Evaluates program env (.subscript (.name "seen") tupleExpr) heap value
      (heap ++ [.tuple (stateValues n index)]) globals := by
  let middle := heap ++ [.tuple (stateValues n index)]
  have appended := found_append found [.tuple (stateValues n index)]
  have hashed := hash_state n index middle heap.length (by simp [middle])
  dsimp only [middle] at hashed
  apply Evaluates.subscript (by intro a b c impossible; cases impossible)
    (Evaluates.lookup getSeen) (tuple_evaluates n index heap env getM getD getA)
  rcases appended with got | ⟨rfl, got⟩
  · simp [Mutable.getItem, got, hashed, selected]
  · simp at selected

end data.«project-euler-statements».data.py.project_euler_statements.p64
