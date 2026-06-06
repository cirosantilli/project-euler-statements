from common import proper_divisor_sum


def divisor_sum(n: int) -> int:
    return proper_divisor_sum(n)


def is_abundant(n: int) -> bool:
    return divisor_sum(n) > n


def abundant_set(limit: int) -> set[int]:
    return {n for n in range(1, limit + 1) if is_abundant(n)}


def naive(limit: int) -> int:
    abundants = abundant_set(limit)
    can = set()
    for a in abundants:
        for b in abundants:
            can.add(a + b)
    return sum(n for n in range(1, limit + 1) if n not in can)


if __name__ == '__main__':
    assert is_abundant(12)
    assert 24 == 12 + 12

