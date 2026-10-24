import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p12.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P12

namespace data.«project-euler-statements».data.py.project_euler_statements.p12
open FormalSW.PyAst
private abbrev program := P12Ast.module

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["triangle", "divisor_count", "naive"] at member
    simp at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem triangle.result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "triangle" [.scalar (.int n)] heap
      (.scalar (.int (n * (n + 1) / 2))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.binary
    (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl)
      (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant rfl) rfl)
    HeapCalls.Evaluates.constant rfl)

theorem triangle.natural (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "triangle" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P12.triangle n))) heap := by
  simpa [ProjectEulerStatements.P12.triangle, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using triangle.result n heap

theorem triangle.«Returns» (n : Int) : (scalarFunction program "triangle" [.int n]).Returns :=
  ⟨.int (n * (n + 1) / 2), .done rfl⟩

private abbrev divisorObject (n : Nat) : Mutable.Object :=
  .list ((ProjectEulerStatements.DivisorEnumeration.values n).map (fun (value : Nat) => .scalar (.int (value : Int))))

theorem divisor_count.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "divisor_count" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P12.divisorCount n))) (heap ++ [divisorObject n]) := by
  have called := (common.divisors.result n heap).extend common_extension
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.builtin (.cons
    (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) called) .nil)
  simp [HeapCalls.primitive, Mutable.length, ProjectEulerStatements.P12.divisorCount_eq_enumeration_length]

private theorem divisor_count.negative (n : Int) (negative : n < 0) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "divisor_count" [.scalar (.int n)] heap (.scalar (.int 0)) (heap ++ [.list []]) := by
  have called := (common.divisors.negative n negative heap).extend common_extension
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.builtin (.cons
    (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) called) .nil)
  simp [HeapCalls.primitive, Mutable.length]

theorem divisor_count.«Returns» (n : Int) :
    (HeapCalls.scalarFunction program "divisor_count" [.int n]).Returns := by
  by_cases nonnegative : 0 ≤ n
  · simpa [Int.toNat_of_nonneg nonnegative] using ((divisor_count.result n.toNat []).scalar_returns (values := [.int (n.toNat : Int)]))
  · exact (divisor_count.negative n (by omega) []).scalar_returns

theorem divisor_count.«Supported» (n : Int) :
    (HeapCalls.scalarFunction program "divisor_count" [.int n]).Supported :=
  (divisor_count.«Returns» n).supported

private abbrev loopBody : List Stmt :=
  [.assign [.name "t"] (.call (.name "triangle") [.name "n"]),
    .ifThen (.compare (.call (.name "divisor_count") [.name "t"]) [(.gt, .name "k")]) [.return (.name "t")] [],
    .augAssign (.name "n") .add (.constant (.int 1))]
private abbrev loop : List Stmt := [.whileDo (.constant (.bool true)) loopBody []]

/-- A mathematical existence witness bounds the search proof, not the Python
execution. Each iteration preserves the input heap and appends one private list. -/
private theorem naive.loop (heap : Mutable.Heap) (k n : Nat)
    (before : n ≤ Nat.find (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k))
    (env : HeapCalls.Env)
    (getN : env "n" = some (.scalar (.int n))) (getK : env "k" = some (.scalar (.int k))) :
    ∃ extra, HeapCalls.BlockReturns program env loop heap
      (.scalar (.int (ProjectEulerStatements.P12.firstTriangleOver k))) (heap ++ extra) := by
  let t := ProjectEulerStatements.P12.triangle n
  let withT := HeapCalls.setLocal env "t" (.scalar (.int t))
  let nextHeap := heap ++ [divisorObject t]
  have calculated : HeapCalls.Evaluates program env (.call (.name "triangle") [.name "n"]) heap
      (.scalar (.int t)) heap :=
    HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup getN) .nil) (triangle.natural n heap)
  have count : HeapCalls.Evaluates program withT (.call (.name "divisor_count") [.name "t"]) heap
      (.scalar (.int (ProjectEulerStatements.P12.divisorCount t))) nextHeap :=
    HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (divisor_count.result t heap)
  have tested : HeapCalls.Evaluates program withT
      (.compare (.call (.name "divisor_count") [.name "t"]) [(.gt, .name "k")]) heap
      (.scalar (.bool (decide (k < ProjectEulerStatements.P12.divisorCount t)))) nextHeap :=
    HeapCalls.Evaluates.compare count
      (HeapCalls.Evaluates.lookup (by simpa [withT, HeapCalls.setLocal] using getK))
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases qualifies : k < ProjectEulerStatements.P12.divisorCount t
  · have least := Nat.find_min' (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k) qualifies
    have same : n = Nat.find (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k) := by omega
    refine ⟨[divisorObject t], ?_⟩
    apply HeapCalls.BlockReturns.while_loop (flag := true) HeapCalls.Evaluates.constant rfl
    apply HeapCalls.BlockReturns.assign calculated
    apply HeapCalls.BlockReturns.branch (flag := true) (by simpa [qualifies] using tested) rfl
    exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup
      (by simp [HeapCalls.setLocal, ProjectEulerStatements.P12.firstTriangleOver, t, same]))
  · have earlier : n < Nat.find (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k) := by
      have witness := Nat.find_spec (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k)
      by_contra late
      have same : n = Nat.find (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k) := by omega
      apply qualifies
      simpa only [t, same] using witness
    let nextEnv := HeapCalls.setLocal withT "n" (.scalar (.int (↑(n + 1))))
    obtain ⟨extra, rest⟩ := naive.loop nextHeap k (n + 1) (by omega) nextEnv rfl
      (by simpa [nextEnv, withT, HeapCalls.setLocal] using getK)
    refine ⟨divisorObject t :: extra, ?_⟩
    apply HeapCalls.BlockReturns.while_loop (flag := true) HeapCalls.Evaluates.constant rfl
    apply HeapCalls.BlockReturns.assign calculated
    apply HeapCalls.BlockReturns.branch (flag := false) (by simpa [qualifies] using tested) rfl
    apply HeapCalls.BlockReturns.augAssign
      (by simpa [withT, HeapCalls.setLocal] using getN) HeapCalls.Evaluates.constant
      (value := .scalar (.int (↑(n + 1)))) (afterOperation := nextHeap)
    · simp [HeapCalls.inplace, Mutable.binary, scalarBinary]
    · simpa [nextHeap, loop, loopBody, Calls.loopContinuation, Calls.loopControl, List.append_assoc] using rest
termination_by Nat.find (ProjectEulerStatements.P12.exists_triangle_divisorCount_gt k) - n
decreasing_by omega

/-- The source returns the mathematical least triangular number for every
nonnegative threshold, with no search cutoff. -/
theorem naive.result (k : Nat) (heap : Mutable.Heap) :
    ∃ extra, HeapCalls.ReturnsValue program "naive" [.scalar (.int k)] heap
      (.scalar (.int (ProjectEulerStatements.P12.naive k))) (heap ++ extra) := by
  let env := HeapCalls.setLocal (HeapCalls.argumentEnv [⟨"k", some (.name "int"), none⟩] [.scalar (.int k)])
    "n" (.scalar (.int 0))
  obtain ⟨extra, rest⟩ := naive.loop heap k 0 (Nat.zero_le _) env rfl rfl
  refine ⟨extra, HeapCalls.BlockReturns.function rfl rfl ?_⟩
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  simpa [ProjectEulerStatements.P12.naive_eq_firstTriangleOver] using rest

private theorem naive.negative (k : Int) (negative : k < 0) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "naive" [.scalar (.int k)] heap (.scalar (.int 0)) (heap ++ [.list []]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.while_loop (flag := true) HeapCalls.Evaluates.constant rfl
  apply HeapCalls.BlockReturns.assign
    (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (triangle.natural 0 heap))
  apply HeapCalls.BlockReturns.branch (flag := true) (middle := heap ++ [.list []]) (value := .scalar (.bool true))
  · apply HeapCalls.Evaluates.compare
      (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (divisor_count.result 0 heap))
      (HeapCalls.Evaluates.lookup rfl)
    simpa [HeapCalls.compare, scalarCompare, evalCmpOp, ProjectEulerStatements.P12.divisorCount,
      ProjectEulerStatements.P12.divisors, ProjectEulerStatements.DivisorEnumeration.values] using negative
  · rfl
  · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup rfl)

theorem naive.«Returns» (k : Int) : (HeapCalls.scalarFunction program "naive" [.int k]).Returns := by
  by_cases nonnegative : 0 ≤ k
  · obtain ⟨extra, executed⟩ := naive.result k.toNat []
    simpa [Int.toNat_of_nonneg nonnegative] using (executed.scalar_returns (values := [.int (k.toNat : Int)]))
  · exact (naive.negative k (by omega) []).scalar_returns

theorem naive.«Supported» (k : Int) : (HeapCalls.scalarFunction program "naive" [.int k]).Supported :=
  (naive.«Returns» k).supported

end data.«project-euler-statements».data.py.project_euler_statements.p12
