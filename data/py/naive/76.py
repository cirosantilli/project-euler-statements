from functools import lru_cache


@lru_cache(None)
def count_ways(n: int, max_: int) -> int:
    if n == 0:
        return 1
    if max_ == 0:
        return 0
    return (count_ways(n - max_, max_) if max_ <= n else 0) + count_ways(n, max_ - 1)


def naive(n: int) -> int:
    return count_ways(n, n - 1)


if __name__ == '__main__':
    assert naive(5) == 6

