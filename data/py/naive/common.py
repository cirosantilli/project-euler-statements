from __future__ import annotations

from functools import lru_cache, reduce
from itertools import combinations, permutations
from math import gcd, isqrt, comb, factorial, prod, log


def digits_le(n: int, base: int = 10) -> list[int]:
    if n == 0:
        return []
    out = []
    while n:
        out.append(n % base)
        n //= base
    return out


def digits_be(n: int, base: int = 10) -> list[int]:
    return list(reversed(digits_le(n, base)))


def of_digits_le(ds: list[int], base: int = 10) -> int:
    n = 0
    mul = 1
    for d in ds:
        n += d * mul
        mul *= base
    return n


def of_digits_be(ds: list[int], base: int = 10) -> int:
    return of_digits_le(list(reversed(ds)), base)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    r = isqrt(n)
    p = 3
    while p <= r:
        if n % p == 0:
            return False
        p += 2
    return True


def proper_divisor_sum(n: int) -> int:
    return sum(d for d in range(1, n) if n % d == 0) if n else 0


def proper_divisors(n: int) -> list[int]:
    return [d for d in range(1, n) if n % d == 0]


def divisors(n: int) -> list[int]:
    if n == 0:
        return []
    return [d for d in range(1, n + 1) if n % d == 0]


def erase_dups(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


def sublists(xs):
    out = [[]]
    for x in xs:
        out += [[x] + ys for ys in out]
    return out

