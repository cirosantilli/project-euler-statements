"""
@formalsw: theorem is_cyclic_pair_source_result
  (left right : Int) (heap : FormalSW.PyAst.Mutable.Heap) (globals : FormalSW.PyAst.Mutable.Globals) :
  FormalSW.PyAst.HeapCalls.ReturnsValue P61Ast.module "is_cyclic_pair"
    [.scalar (.int left), .scalar (.int right)] heap
    (.scalar (.bool (ProjectEulerSolutions.PolygonalCycle.links left right))) heap globals

@formalsw: theorem families_source_result
  (limit : Int) (caller : FormalSW.PyAst.Mutable.Heap) (env : FormalSW.PyAst.HeapCalls.Env)
  (globals : FormalSW.PyAst.Mutable.Globals) :
  env "limit" = some (.scalar (.int limit)) →
  FormalSW.PyAst.HeapCalls.BlockContinues P61Ast.module env
    ((FormalSW.PyAst.executableBody
      ((FormalSW.PyAst.findFunctionIn P61Ast.module.body "naive").getD ([], [])).2).take 1)
    caller (data.«project-euler-statements».data.py.project_euler_statements.p61.families.setupEnv env caller limit)
    (data.«project-euler-statements».data.py.project_euler_statements.p61.families.setupHeap caller limit) globals

@formalsw: theorem extend_base_source_result
  (values : List Int) (heap : FormalSW.PyAst.Mutable.Heap) (path remaining : Nat)
  (familiesCell : FormalSW.PyAst.Mutable.Value) (globals : FormalSW.PyAst.Mutable.Globals) :
  values ≠ [] →
  heap[path]? = some (.list (values.map (fun value => .scalar (.int value)))) →
  heap[remaining]? = some (.list []) →
  FormalSW.PyAst.HeapCalls.ReturnsValue P61Ast.module "__formalsw_local_naive_extend"
    [.ref path, .ref remaining, familiesCell] heap
    (.scalar (.int (if ProjectEulerSolutions.PolygonalCycle.closed values then values.sum else 0))) heap globals

@formalsw: theorem extend_source_result
  (fuel : Nat) (heap : FormalSW.PyAst.Mutable.Heap) (path remainingAddress familiesCell : Nat) (limit : Int)
  (values : List Int) (remaining : List Nat)
  (state : data.«project-euler-statements».data.py.project_euler_statements.p61.extend.SearchState
    heap path remainingAddress familiesCell limit values remaining)
  (globals : FormalSW.PyAst.Mutable.Globals) :
  values ≠ [] → remaining.length ≤ fuel →
  ∃ extra, FormalSW.PyAst.HeapCalls.ReturnsValue P61Ast.module "__formalsw_local_naive_extend"
    [.ref path, .ref remainingAddress, .ref familiesCell] heap
    (.scalar (.int (ProjectEulerSolutions.PolygonalCycle.extend limit fuel values remaining))) (heap ++ extra) globals

@formalsw: theorem naive_source_result
  (limit : Int) (caller : FormalSW.PyAst.Mutable.Heap) (globals : FormalSW.PyAst.Mutable.Globals) :
  ∃ extra, FormalSW.PyAst.HeapCalls.ReturnsValue P61Ast.module "naive" [.scalar (.int limit)] caller
    (.scalar (.int (ProjectEulerSolutions.PolygonalCycle.reference limit))) (caller ++ extra) globals
"""
from __future__ import annotations

from collections.abc import Callable


def p3(n: int) -> int:
    return n * (n + 1) // 2


def p4(n: int) -> int:
    return n * n


def p5(n: int) -> int:
    return n * (3 * n - 1) // 2


def p6(n: int) -> int:
    return n * (2 * n - 1)


def p7(n: int) -> int:
    return n * (5 * n - 3) // 2


def p8(n: int) -> int:
    return n * (3 * n - 2)


def polygonal(sides: int, index: int) -> int:
    """
    @formalsw: Returns
    """
    return index * ((sides - 2) * index - (sides - 4)) // 2


def last_two(n: int) -> int:
    return n % 100


def first_two(n: int) -> int:
    return n // 100


def is_cyclic_pair(a: int, b: int) -> bool:
    return last_two(a) == first_two(b)


def is_cyclic_list(xs: list[int]) -> bool:
    if len(xs) < 2:
        return False
    return all(is_cyclic_pair(a, b) for a, b in zip(xs, xs[1:])) and is_cyclic_pair(xs[-1], xs[0])


def four_digit(f: Callable[[int], int], limit: int) -> list[int]:
    return [f(i) for i in range(limit + 1) if 1000 <= f(i) < 10000]


def naive(limit: int) -> int:
    """
    @formalsw: Returns
    Enumerate every type order, scanning whole families for each next value.
    Fix the first type to triangular; every valid cycle has that rotation.
    """
    families = [
        [polygonal(sides, n) for n in range(limit + 1) if 1000 <= polygonal(sides, n) < 10000]
        for sides in range(3, 9)
    ]

    def extend(path: list[int], remaining: list[int]) -> int:
        if not remaining:
            if is_cyclic_pair(path[-1], path[0]):
                return sum(path)
            return 0

        best = 0
        for kind in remaining:
            unused = [other for other in remaining if other != kind]
            for value in families[kind]:
                if value in path:
                    continue
                if not is_cyclic_pair(path[-1], value):
                    continue
                best = max(best, extend(path + [value], unused))
        return best

    best = 0
    for start in families[0]:
        best = max(best, extend([start], [1, 2, 3, 4, 5]))
    return best


def naive_default() -> int:
    """
    @formalsw: Returns
    """
    # P_3,141 = 10011; the other five families grow at least as quickly.
    return naive(140)


if __name__ == "__main__":
    assert is_cyclic_list([8128, 2882, 8281])
    assert is_cyclic_list([8256, 5625, 2512, 1281, 8128, 2882])
    assert naive(-1) == 0
    assert naive(0) == 0
    assert naive(20) == 0
    assert naive_default() == 28684
