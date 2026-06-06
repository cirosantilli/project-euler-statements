from functools import lru_cache
from common import digits_le


@lru_cache(None)
def fib(n: int) -> int:
    if n == 0:
        return 0
    if n == 1:
        return 1
    return fib(n - 1) + fib(n - 2)


def num_digits(n: int) -> int:
    return len(digits_le(n))


def naive(n: int) -> int:
    i = 0
    while True:
        if n <= num_digits(fib(i)):
            return i
        i += 1


if __name__ == '__main__':
    assert fib(12) == 144
    assert naive(3) == 12

