from math import isqrt
from common import is_prime


def primes_below(limit: int) -> list[int]:
    return [n for n in range(limit) if is_prime(n)]


def naive(limit: int) -> int:
    ps = primes_below(isqrt(limit) + 1)
    sums = []
    for p in ps:
        for q in ps:
            for r in ps:
                s = p ** 2 + q ** 3 + r ** 4
                if s < limit:
                    sums.append(s)
    return len(set(sums))


if __name__ == '__main__':
    assert naive(50) == 4

