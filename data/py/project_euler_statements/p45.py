def tri(n: int) -> int:
    return n * (n + 1) // 2


def pent(n: int) -> int:
    return n * (3 * n - 1) // 2


def hex(n: int) -> int:
    return n * (2 * n - 1)


def is_pent(x: int) -> bool:
    """
    @formalsw: Returns
    """
    return any(pent(n) == x for n in range(x + 1))


def is_hex(x: int) -> bool:
    """
    @formalsw: Returns
    """
    return any(hex(n) == x for n in range(x + 1))


def naive(after: int = 40755) -> int:
    """
    @formalsw: Returns
    """
    i = 1
    j = 1
    k = 1
    while True:
        t, p, h = tri(i), pent(j), hex(k)
        if t == p == h and t > after:
            return t
        if t <= p and t <= h:
            i += 1
        elif p <= h:
            j += 1
        else:
            k += 1


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert tri(285) == 40755
    assert pent(165) == 40755
    assert hex(143) == 40755

