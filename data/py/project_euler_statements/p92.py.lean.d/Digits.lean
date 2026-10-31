import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p92.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.DigitSquareChains
import lang.py.FormalSW.SumCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p92
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.DigitSquareChains
set_option Elab.async false

abbrev program := P92Ast.module
abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
def digits (n : Nat) := (Nat.digits 10 n).map number

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["next_term", "ends_at_89", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem square_fold (values : List Nat) (initial : Int) :
    values.foldl (fun (total : Int) d => total + ((d * d : Nat) : Int)) initial =
      initial + (((values.map (fun d => d * d)).sum : Nat) : Int) := by
  induction values generalizing initial with
  | nil => simp
  | cons head rest ih =>
      simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, Int.natCast_add, Int.add_assoc]

/-- The source allocates the decimal digit list, then consumes its generator without modifying that list. -/
theorem next_term.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "next_term" [number n] heap (number (nextTerm n))
      (heap ++ [.list (digits n)]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have converted := (common.digits_le.decimal n heap globals).extend common_extension
  have total : (Nat.digits 10 n).foldl (fun (total : Int) d => total + ((d * d : Nat) : Int)) 0 =
      (nextTerm n : Int) := by simpa [nextTerm] using square_fold (Nat.digits 10 n) 0
  change Evaluates program _ _ heap (.scalar (.int (nextTerm n))) _ globals
  rw [← total]
  apply Evaluates.sum_generator_sequence
    (items := digits n) (by intro expressions; simp)
    (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) converted)
    (by simp [Mutable.sequence, digits]) Evaluates.constant rfl
  apply sum_map_loop (values := Nat.digits 10 n) (encode := number)
    (number := fun d => ((d * d : Nat) : Int)) (Nat.digits 10 n) (by decide)
  · simp [sequenceValue, sequenceSource, Mutable.sequence]
  · intro env digit found
    exact Evaluates.binary (av := number digit) (bv := number digit)
      (Evaluates.lookup found) (Evaluates.lookup found)
      (by simp [Mutable.binary, scalarBinary])
  · rfl
  · simp [setLocal]

end data.«project-euler-statements».data.py.project_euler_statements.p92
