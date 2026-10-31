from functools import lru_cache


@lru_cache(None)
def count_ways(n: int, max_: int) -> int:
    """
    Count partitions using positive parts at most max_, including the empty sum at zero.

    @formalsw: Returns
    """
    if n == 0:
        return 1
    if n < 0:
        return 0
    if max_ <= 0:
        return 0
    return (count_ways(n - max_, max_) if max_ <= n else 0) + count_ways(n, max_ - 1)


def naive(n: int) -> int:
    """
    Count partitions using positive parts strictly smaller than n.

    @formalsw: Returns
    """
    return count_ways(n, n - 1)


if __name__ == '__main__':
    assert naive(5) == 6

