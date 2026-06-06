from math import gcd
from common import digits_le, of_digits_le


def erase_nth(xs: list[int], i: int) -> list[int]:
    return xs[:i] + xs[i + 1:]


def is_curious(n: int, d: int) -> bool:
    dn, dd = digits_le(n), digits_le(d)
    if not (len(dn) == len(dd) and 2 <= len(dn) and n < d):
        return False
    for i, x in enumerate(dn):
        for j, y in enumerate(dd):
            if x == y and x != 0:
                np = of_digits_le(erase_nth(dn, i))
                dp = of_digits_le(erase_nth(dd, j))
                if n * dp == d * np:
                    return True
    return False


def curious_fractions() -> list[tuple[int, int]]:
    return [(n, d) for n in range(100) for d in range(100) if is_curious(n, d)]


def naive() -> int:
    pn, pd = 1, 1
    for n, d in curious_fractions():
        pn *= n
        pd *= d
    return pd // gcd(pn, pd)


if __name__ == '__main__':
    assert is_curious(49, 98)

