from functools import lru_cache


@lru_cache(None)
def partition_go(n: int, max_: int) -> int:
    if n == 0:
        return 1
    if max_ == 0:
        return 0
    return (partition_go(n - max_, max_) if max_ <= n else 0) + partition_go(n, max_ - 1)


def partition(n: int) -> int:
    return partition_go(n, n)


def naive(mod: int) -> int:
    n = 1
    while True:
        if partition(n) % mod == 0:
            return n
        n += 1


if __name__ == '__main__':
    assert partition(5) == 7
    assert naive(1) == 1
    assert naive(5) == 4
    assert naive(7) == 5

