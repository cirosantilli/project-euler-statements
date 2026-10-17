def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    if n == 0:
        return 0
    m = n - 1
    s = naive(m)
    return s + m if m % 3 == 0 or m % 5 == 0 else s


def naive2(max_: int) -> int:
    """
    @formalsw: Requires(max_ >= 0)
    @formalsw: Equiv(naive)
    """
    return sum(x for x in range(max_) if x % 3 == 0 or x % 5 == 0)


if __name__ == '__main__':
    assert naive(10) == 23

