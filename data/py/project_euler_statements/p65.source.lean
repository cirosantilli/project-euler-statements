import data.«project-euler-statements».data.py.project_euler_statements.«p65.convergents.source»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»

namespace data.«project-euler-statements».data.py.project_euler_statements.p65
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.EConvergents
set_option Elab.async false
private abbrev program := P65Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev digits (n : Nat) := (Nat.digits 10 n).map number

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 6 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["coeff_e", "coeffs", "convergent_num", "digit_sum", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem digit_sum.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "digit_sum" [number n] heap (number (Nat.digits 10 n).sum)
      (heap ++ [.list (digits n)]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have converted := (common.digits_le.decimal n heap globals).extend common_extension
  have total : ((Nat.digits 10 n).map (fun d : Nat => (d : Int))).foldl Int.add 0 =
      ((Nat.digits 10 n).sum : Int) := by
    have folded := List.foldl_map_hom (g := fun d : Nat => (d : Int))
      (f := Nat.add) (f' := Int.add) (a := 0) (l := (Nat.digits 10 n))
      (by intro a b; exact (Nat.cast_add a b).symm)
    exact folded.trans (congrArg (fun value : Nat => (value : Int))
      (List.sum_eq_foldl_nat (xs := Nat.digits 10 n)).symm)
  change Evaluates program _ _ heap (.scalar (.int ((Nat.digits 10 n).sum : Int))) _ globals
  rw [← total]
  apply Evaluates.sum_integers (initial := 0) (values := (Nat.digits 10 n).map (fun d : Nat => (d : Int)))
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) converted)
      (.cons Evaluates.constant .nil)
  · simp [Mutable.sequence, digits, List.map_map, Function.comp_def]

theorem naive.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number n] heap (number (answer n)) (heap ++ extra) globals := by
  obtain ⟨extra, converted⟩ := convergent_num.result n heap globals
  refine ⟨extra ++ [.list (digits (numerator n))], ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call (middle := heap ++ extra) (values := [number (numerator n)])
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) converted) .nil
  · simpa only [List.append_assoc, answer] using digit_sum.result (numerator n) (heap ++ extra) globals

end data.«project-euler-statements».data.py.project_euler_statements.p65
