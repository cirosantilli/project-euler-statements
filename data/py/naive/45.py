def tri(n: int) -> int: return n * (n + 1) // 2

def pent(n: int) -> int: return n * (3 * n - 1) // 2

def hex(n: int) -> int: return n * (2 * n - 1)


def is_pent(x: int) -> bool:
    return any(pent(n) == x for n in range(x + 1))


def is_hex(x: int) -> bool:
    return any(hex(n) == x for n in range(x + 1))


def naive(start: int, limit: int) -> int:
    for i in range(limit + 1):
        t = tri(start + i)
        if is_pent(t) and is_hex(t):
            return t
    return 0


if __name__ == '__main__':
    assert tri(285) == 40755
    assert pent(165) == 40755
    assert hex(143) == 40755

