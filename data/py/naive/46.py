from common import is_prime


def is_odd_composite(n: int) -> bool:
    return n % 2 == 1 and not is_prime(n) and n > 1


def can_be_written(n: int) -> bool:
    return any(is_prime(p) and any(p + 2 * k ** 2 == n for k in range(n)) for p in range(n))


def naive(limit: int) -> int:
    for n in range(limit):
        if is_odd_composite(n) and not can_be_written(n):
            return n
    return 0


if __name__ == '__main__':
    assert 9 == 7 + 2 * 1 ** 2
    assert 33 == 31 + 2 * 1 ** 2

