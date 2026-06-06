from functools import lru_cache
from common import is_prime


@lru_cache(None)
def diag_prime_count(k: int) -> int:
    if k == 0:
        return 0
    side = 2 * k + 1
    sq = side ** 2
    step = side - 1
    corners = [sq, sq - step, sq - 2 * step, sq - 3 * step]
    return diag_prime_count(k - 1) + sum(1 for c in corners if is_prime(c))


def diag_total(k: int) -> int:
    side = 2 * k + 1
    return 2 * side - 1


def ratio_below(k: int, num: int, den: int) -> bool:
    return den * diag_prime_count(k) < num * diag_total(k)


def naive(num: int, den: int) -> int:
    k = 0
    while True:
        if ratio_below(k, num, den):
            return 2 * k + 1
        k += 1


if __name__ == '__main__':
    assert diag_prime_count(3) == 8
    assert diag_total(3) == 13

