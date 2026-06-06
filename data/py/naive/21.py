from common import proper_divisor_sum


def d(n: int) -> int:
    return proper_divisor_sum(n)


def is_amicable(n: int) -> bool:
    m = d(n)
    return m != n and d(m) == n


def naive(limit: int) -> int:
    return sum(n for n in range(1, limit) if is_amicable(n))


if __name__ == '__main__':
    assert d(220) == 284
    assert d(284) == 220

