from math import gcd


def naive(limit: int) -> int:
    return sum(1 for d in range(limit + 1) for n in range(d) if n < d and gcd(n, d) == 1 and n * 2 < d and n * 3 > d)


if __name__ == '__main__':
    assert naive(8) == 3

