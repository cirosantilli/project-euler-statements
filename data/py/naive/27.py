from common import is_prime


def quad(a: int, b: int, n: int) -> int:
    return n * n + a * n + b


def is_prime_int(z: int) -> bool:
    return z > 1 and is_prime(z)


def consec_prime_len(a: int, b: int) -> int:
    bound = abs(b) + 1
    n = 0
    while n < bound and is_prime_int(quad(a, b, n)):
        n += 1
    return n


def naive(limit_a: int, limit_b: int) -> int:
    pairs = [(a, b) for a in range(-limit_a, limit_a + 1) for b in range(-limit_b, limit_b + 1)]
    a, b = max(pairs, key=lambda p: consec_prime_len(p[0], p[1])) if pairs else (0, 0)
    return a * b


if __name__ == '__main__':
    assert consec_prime_len(1, 41) == 40
    assert consec_prime_len(-79, 1601) == 80
    assert -79 * 1601 == -126479

