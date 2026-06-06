from functools import lru_cache


@lru_cache(None)
def fib(n: int) -> int:
    if n == 0:
        return 1
    if n == 1:
        return 2
    return fib(n - 2) + fib(n - 1)


def naive(n: int) -> int:
    i = 0
    total = 0
    while True:
        f = fib(i)
        if f <= n:
            if f % 2 == 0:
                total += f
            i += 1
        else:
            return total

