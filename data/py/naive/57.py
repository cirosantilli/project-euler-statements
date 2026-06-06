from functools import lru_cache
from common import digits_le


def next_frac(p: int, q: int) -> tuple[int, int]:
    return p + 2 * q, p + q


@lru_cache(None)
def convergent(n: int) -> tuple[int, int]:
    if n == 0:
        return 3, 2
    return next_frac(*convergent(n - 1))


def naive(k: int) -> int:
    return sum(1 for i in range(k) if len(digits_le(convergent(i)[0])) > len(digits_le(convergent(i)[1])))


if __name__ == '__main__':
    t = convergent(7)
    assert len(digits_le(t[0])) > len(digits_le(t[1]))

