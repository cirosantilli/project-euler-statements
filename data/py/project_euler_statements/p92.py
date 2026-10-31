from .common import digits_le


def next_term(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sum(d * d for d in digits_le(n))


def ends_at_89(n: int) -> bool:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    x = n
    seen = []
    while x not in (1, 89) and x not in seen:
        seen.append(x)
        x = next_term(x)
    return x == 89


def naive(limit_exclusive: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(1 for n in range(1, limit_exclusive) if ends_at_89(n))


if __name__ == '__main__':
    assert not ends_at_89(44)
    assert ends_at_89(85)
    assert ends_at_89(2)
    assert not ends_at_89(0)

