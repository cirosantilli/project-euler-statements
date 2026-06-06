def strip_factor(p: int, n: int) -> int:
    if p <= 1:
        return n
    while n and n % p == 0:
        n //= p
    return n


def reduced_denom(n: int) -> int:
    return strip_factor(5, strip_factor(2, n))


def cycle_len_aux(d: int) -> int:
    if d == 0:
        return 0
    r, k = 10 % d, 1
    for _ in range(d):
        if r == 1:
            return k
        r = (r * 10) % d
        k += 1
    return 0


def cycle_len(d: int) -> int:
    d2 = reduced_denom(d)
    return 0 if d2 == 1 else cycle_len_aux(d2)


def naive(limit: int) -> int:
    return max(range(limit), key=cycle_len) if limit > 0 else 0


if __name__ == '__main__':
    assert cycle_len(7) == 6
    assert cycle_len(6) == 1

