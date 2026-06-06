from functools import lru_cache


def collatz_step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


@lru_cache(None)
def collatz_len(n: int) -> int:
    if n == 0:
        return 0
    if n == 1:
        return 1
    return 1 + collatz_len(collatz_step(n))


def naive(limit: int) -> int:
    return max(range(limit + 1), key=collatz_len) if limit >= 0 else 0


if __name__ == '__main__':
    assert collatz_len(13) == 10

