from functools import lru_cache
from common import is_prime


def primes_up_to(n: int) -> tuple[int, ...]:
    return tuple(x for x in range(n + 1) if is_prime(x))


@lru_cache(None)
def go(n: int, ps: tuple[int, ...]) -> int:
    if n == 0:
        return 1
    if not ps:
        return 0
    p, rest = ps[0], ps[1:]
    if p == 0:
        return go(n, rest)
    return (go(n - p, ps) if p <= n else 0) + go(n, rest)


def count_prime_sums(n: int) -> int:
    return go(n, primes_up_to(n))


def naive(limit: int, target: int) -> int:
    for n in range(limit + 1):
        if count_prime_sums(n) > target:
            return n
    return 0


if __name__ == '__main__':
    assert count_prime_sums(10) == 5

