from math import gcd


def count_reduced(d: int) -> int:
    return sum(1 for n in range(d) if n < d and gcd(n, d) == 1)


def naive(limit: int) -> int:
    return sum(count_reduced(d) for d in range(limit + 1) if d > 1)


if __name__ == '__main__':
    assert naive(8) == 21

