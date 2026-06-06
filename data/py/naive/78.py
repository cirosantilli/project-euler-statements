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


def naive(limit: int) -> int:
    for n in range(limit + 1):
        if partition(n) % 1000000 == 0:
            return n
    return 0


if __name__ == '__main__':
    assert partition(5) == 7

