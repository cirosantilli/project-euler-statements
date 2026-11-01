from .common import digits_le


def digits_key(n: int) -> list[int]:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sorted(digits_le(n))


def _count_window(limit: int, n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    key = digits_key(n ** 3)
    return sum(1 for i in range(1, limit + 1) if digits_key(i ** 3) == key)


def _search_window(limit: int, target: int) -> int:
    """
    @formalsw: Returns
    """
    for n in range(1, limit + 1):
        if _count_window(limit, n) == target:
            return n ** 3
    return 0


def cube_perm_count(n: int) -> int:
    """
    Count every positive cube with the same decimal digits as n**3.

    The exclusive root bound is derived from the cube's digit width.
    """
    stop = 1
    ceiling = 10 ** len(digits_key(n ** 3))
    while stop ** 3 < ceiling:
        stop += 1
    return _count_window(stop - 1, n)


def naive(target: int) -> int:
    digits = 1
    stop = 1
    while True:
        while stop ** 3 < 10 ** digits:
            stop += 1
        result = _search_window(stop - 1, target)
        if result != 0:
            return result
        digits += 1


if __name__ == '__main__':
    assert cube_perm_count(345) == 3
