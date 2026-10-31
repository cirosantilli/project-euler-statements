from math import factorial
from .common import digits_le


def next_term(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sum(factorial(d) for d in (digits_le(n) if n else [0]))


def chain_len(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    x, seen = n, []
    while x not in seen:
        seen.append(x)
        x = next_term(x)
    return len(seen)


def naive(limit: int, target: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(1 for n in range(1, limit) if chain_len(n) == target)


if __name__ == '__main__':
    assert chain_len(69) == 5
    assert chain_len(78) == 4
    assert chain_len(540) == 2
    assert chain_len(3) == 16
    assert chain_len(0) == 2

