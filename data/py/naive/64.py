from math import isqrt


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def period_len(n: int) -> int:
    a0 = isqrt(n)
    if is_square(n):
        return 0
    m, d, a = 0, 1, a0
    for _ in range(n + 1):
        m = d * a - m
        d = (n - m * m) // d
        a = (a0 + m) // d
        if a == 2 * a0:
            return 1
    return 0


def period_len_full(n: int) -> int:
    a0 = isqrt(n)
    if is_square(n):
        return 0
    m, d, a = 0, 1, a0
    cnt = 0
    for _ in range(n + 1):
        m = d * a - m
        d = (n - m * m) // d
        a = (a0 + m) // d
        cnt += 1
        if a == 2 * a0:
            return cnt
    return 0


def naive(limit: int) -> int:
    return sum(1 for n in range(limit + 1) if period_len_full(n) % 2 == 1)


if __name__ == '__main__':
    assert naive(13) == 4

