from .common import is_prime


def pow10_for(n: int) -> int:
    # Smallest power of ten strictly greater than n; all callers use primes.
    base = 1
    while base <= n:
        base *= 10
    return base


def concat(left: int, right: int) -> int:
    return left * pow10_for(right) + right


def pair_ok(left: int, right: int) -> bool:
    return is_prime(concat(left, right)) and is_prime(concat(right, left))


def naive(limit: int = 10000) -> tuple[int, list[int]]:
    # Enumerate increasing five-prime sets, pruning only incompatible prefixes.
    # Neither 2 nor 5 can concatenate with another prime in both directions.
    primes = [p for p in range(3, limit + 1) if p != 5 and is_prime(p)]
    best_sum = 10**30
    best_set: list[int] = []
    for a in primes:
        for b in primes:
            if a < b and pair_ok(a, b):
                for c in primes:
                    if b < c and pair_ok(a, c) and pair_ok(b, c):
                        for d in primes:
                            if c < d and pair_ok(a, d) and pair_ok(b, d) and pair_ok(c, d):
                                for e in primes:
                                    if d < e and pair_ok(a, e) and pair_ok(b, e) and pair_ok(c, e) and pair_ok(d, e):
                                        total = a + b + c + d + e
                                        if total < best_sum:
                                            best_sum = total
                                            best_set = [a, b, c, d, e]
    return best_sum, best_set


if __name__ == '__main__':
    assert pow10_for(0) == 1
    assert pow10_for(9) == 10
    assert pow10_for(10) == 100
    assert concat(3, 109) == 3109
    assert pair_ok(3, 7)
    assert not pair_ok(3, 13)
    assert naive(-1) == (10**30, [])
    assert naive(5) == (10**30, [])
    assert naive(100) == (10**30, [])
