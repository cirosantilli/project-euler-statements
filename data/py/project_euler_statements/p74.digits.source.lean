import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p74.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import ProjectEulerStatements.P74

/-! The reference consumes its actual conditional digit list and lazy factorial generator. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p74
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev program := P74Ast.module
abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
abbrev integer (n : Int) : Mutable.Value := .scalar (.int n)
abbrev numbers (items : List Nat) : List Mutable.Value := items.map number

def sourceDigits (n : Nat) : List Nat := if n = 0 then [0] else Nat.digits 10 n

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["next_term", "chain_len", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem factorial_eq (n : Nat) : Math.factorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Math.factorial, Nat.factorial_succ, ih]

private theorem fold_factorials (items : List Nat) (total : Nat) :
    items.foldl (fun acc digit => acc + Nat.factorial digit) total =
      total + (items.map Nat.factorial).sum := by
  induction items generalizing total with
  | nil => simp
  | cons first rest ih => simp [List.foldl_cons, ih, Nat.add_assoc]

private theorem sum_digits (n : Nat) :
    ((sourceDigits n).map Nat.factorial).sum = ProjectEulerStatements.P74.nextTerm n := by
  by_cases zero : n = 0 <;>
    simp [sourceDigits, ProjectEulerStatements.DigitFactorialChains.nextTerm, zero]

abbrev digitsExpr : Expr := .ifExp (.name "n") (.call (.name "digits_le") [.name "n"])
  (.list [.constant (.int 0)])
abbrev factorialExpr : Expr := .call (.name "factorial") [.name "d"]

theorem digits_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    Evaluates program env digitsExpr heap (.ref heap.length)
      (heap ++ [.list (numbers (sourceDigits n))]) := by
  by_cases zero : n = 0
  · subst n
    apply Evaluates.conditional (flag := false) (Evaluates.lookup getN) rfl
    simpa only [sourceDigits, if_pos rfl, numbers, List.map_cons, List.map_nil] using
      (Evaluates.list (module := program) (env := env) (heap := heap)
        (.cons Evaluates.constant .nil))
  · apply Evaluates.conditional (flag := true) (Evaluates.lookup getN)
      (by simp [Mutable.truth, scalarTruth, zero])
    simpa only [sourceDigits, if_neg zero, numbers] using
      (Evaluates.call (.cons (Evaluates.lookup getN) .nil)
        ((common.digits_le.decimal n heap).extend common_extension))

private theorem digit_loop (values remaining : List Nat) (position total : Nat)
    (heap : Mutable.Heap) (source : SequenceSource) (env : HeapCalls.Env)
    (sequence : Mutable.sequence (sequenceValue source) heap =
      some (.ok (numbers values), heap)) (suffix : values.drop position = remaining)
    (getTotal : env sumAccumulator = some (number total)) :
    BlockReturns program env
      [.sequenceStepLoop "d" source position (sumBody factorialExpr []) [],
        .return (.name sumAccumulator)] heap
      (number (remaining.foldl (fun acc d => acc + Nat.factorial d) total)) heap := by
  induction remaining generalizing position total env with
  | nil =>
      apply BlockReturns.sequence_done sequence
      · have missing : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [numbers, missing]
      · exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | cons head tail ih =>
      have item : values[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockReturns.sequence_step (value := number head) sequence (by simp [numbers, item])
      apply BlockReturns.assign (value := number (total + Nat.factorial head)) (middle := heap)
      · apply Evaluates.binary (av := number total) (bv := number (Nat.factorial head))
          (middle := heap) (afterRight := heap)
          (Evaluates.lookup (by simpa [setLocal, sumAccumulator] using getTotal))
        · apply Evaluates.library_call (values := [number head])
            (.cons (Evaluates.lookup (by simp [setLocal])) .nil) rfl
          change some (Except.map Mutable.Value.scalar (Math.factorialCall [.int head]), heap) = _
          rw [Math.factorialCall_natural, factorial_eq]
          rfl
        · simp [Mutable.binary, scalarBinary, number]
      · apply ih
        · simp [List.drop_add_one_eq_tail_drop, suffix]
        · simp [setLocal]

theorem next_term.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "next_term" [number n] heap
      (number (ProjectEulerStatements.P74.nextTerm n))
      (heap ++ [.list (numbers (sourceDigits n))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (items := numbers (sourceDigits n))
    (by intro expressions; simp) (digits_result n heap _ rfl)
  · simp [Mutable.sequence, numbers]
  · exact Evaluates.constant
  · rfl
  · have scanned := digit_loop (sourceDigits n) (sourceDigits n) 0 0
      (heap ++ [.list (numbers (sourceDigits n))]) (sequenceSource (.ref heap.length))
      (setLocal (comprehensionEnv
        (functionEnv ((findFunctionIn program.body "next_term").getD ([], [])).1
          ((findFunctionIn program.body "next_term").getD ([], [])).2 [number n] [])
        [("d", digitsExpr, [])]) sumAccumulator (number 0))
      (by simp [Mutable.sequence, sequenceValue, sequenceSource, numbers]) rfl rfl
    simpa only [fold_factorials, Nat.zero_add, sum_digits] using scanned

end data.«project-euler-statements».data.py.project_euler_statements.p74
