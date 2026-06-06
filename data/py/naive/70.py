from math import gcd
from common import digits_le


def phi(n: int) -> int:
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def digits_sorted(n: int) -> list[int]:
    return sorted(digits_le(n))


def is_permutation(a: int, b: int) -> bool:
    return digits_sorted(a) == digits_sorted(b)


def better(a: int, b: int) -> bool:
    return False if phi(a) == 0 or phi(b) == 0 else a * phi(b) < b * phi(a)


def naive(limit: int) -> int:
    best = 0
    for n in range(limit + 1):
        if n > 1 and is_permutation(n, phi(n)):
            if best == 0 or better(n, best):
                best = n
    return best


if __name__ == '__main__':
    assert phi(9) == 6
    assert is_permutation(87109, 79180)

