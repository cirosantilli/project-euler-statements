from .common import is_prime


def num_distinct_prime_factors(n: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(1 for p in range(n + 1) if p >= 2 and n % p == 0 and is_prime(p))


def naive(n: int) -> int:
    """
    @formalsw: Returns
    """
    i = 0
    while True:
        if all(num_distinct_prime_factors(i + j) == n for j in range(n)):
            return i
        i += 1


def naive_solver(k: int, run_len: int, start_limit: int) -> int:
    """
    Adapt the diagonal reference when run_len equals k; start_limit only controls the sieve.

    @formalsw: Returns
    """
    return naive(k)


if __name__ == '__main__':
    assert num_distinct_prime_factors(14) == 2
    assert num_distinct_prime_factors(15) == 2
    assert num_distinct_prime_factors(644) == 3
    assert num_distinct_prime_factors(645) == 3
    assert num_distinct_prime_factors(646) == 3
    assert naive(2) == 14
    assert naive(3) == 644

