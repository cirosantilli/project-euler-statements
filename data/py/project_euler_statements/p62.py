"""
@formalsw: theorem cube_perm_count_source_result
  (limit : Int) (n : Nat) (heap : FormalSW.PyAst.Mutable.Heap) :
  ∃ extra, FormalSW.PyAst.HeapCalls.ReturnsValue P62Ast.module "cube_perm_count"
    [.scalar (.int limit), .scalar (.int n)] heap
    (.scalar (.int (data.«project-euler-statements».data.py.project_euler_statements.p62.cube_perm_count.answer limit n)))
    (heap ++ extra)

@formalsw: theorem naive_source_result
  (limit target : Int) (heap : FormalSW.PyAst.Mutable.Heap) :
  ∃ extra, FormalSW.PyAst.HeapCalls.ReturnsValue P62Ast.module "naive"
    [.scalar (.int limit), .scalar (.int target)] heap
    (.scalar (.int (data.«project-euler-statements».data.py.project_euler_statements.p62.naive.answer limit target)))
    (heap ++ extra)
"""
from .common import digits_le


def digits_key(n: int) -> list[int]:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sorted(digits_le(n))


def cube_perm_count(limit: int, n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    key = digits_key(n ** 3)
    return sum(1 for i in range(1, limit + 1) if digits_key(i ** 3) == key)


def naive(limit: int, target: int) -> int:
    """
    @formalsw: Returns
    """
    for n in range(1, limit + 1):
        if cube_perm_count(limit, n) == target:
            return n ** 3
    return 0


if __name__ == '__main__':
    assert cube_perm_count(500, 345) == 3

