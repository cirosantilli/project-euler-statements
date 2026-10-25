from math import isqrt


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def period_len_full(n: int) -> int:
    """
    Find the repeating part of the square-root expansion by recording its states.
    """
    a0 = isqrt(n)
    if is_square(n):
        return 0
    m, d, a = 0, 1, a0
    seen = {}
    while (m, d, a) not in seen:
        seen[(m, d, a)] = len(seen)
        m = d * a - m
        d = (n - m * m) // d
        a = (a0 + m) // d
    return len(seen) - seen[(m, d, a)]


def naive(limit: int) -> int:
    return sum(1 for n in range(limit + 1) if period_len_full(n) % 2 == 1)


if __name__ == "__main__":
    assert period_len_full(0) == 0
    assert period_len_full(1) == 0
    assert period_len_full(2) == 1
    assert period_len_full(3) == 2
    assert period_len_full(23) == 4
    assert naive(-1) == 0
    assert naive(13) == 4
