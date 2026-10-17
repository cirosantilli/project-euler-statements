def triplet_products(n: int) -> set[int]:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    out = set()
    for a in range(1, n + 1):
        for b in range(1, n + 1):
            c = n - a - b
            if a < b < c and a * a + b * b == c * c:
                out.add(a * b * c)
    return out


def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    vals = triplet_products(n)
    return max(vals) if vals else 0


if __name__ == '__main__':
    assert 3 ** 2 + 4 ** 2 == 5 ** 2

