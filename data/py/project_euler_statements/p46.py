from .common import is_prime


def is_odd_composite(n: int) -> bool:
    return n % 2 == 1 and not is_prime(n) and n > 1


def can_be_written(n: int) -> bool:
    k = 1
    while 2 * k * k < n:
        if is_prime(n - 2 * k * k):
            return True
        k += 1
    return False


def naive() -> int:
    n = 9
    while True:
        if is_odd_composite(n) and not can_be_written(n):
            return n
        n += 2


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert 9 == 7 + 2 * 1 ** 2
    assert 33 == 31 + 2 * 1 ** 2

