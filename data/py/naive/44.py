def pentagonal(n: int) -> int:
    return n * (3 * n - 1) // 2


def is_pentagonal(x: int) -> bool:
    return any(pentagonal(n) == x for n in range(x + 1))


def naive(limit: int) -> int:
    vals = []
    for j in range(limit + 1):
        for k in range(j):
            pj, pk = pentagonal(j), pentagonal(k)
            if is_pentagonal(pj + pk) and is_pentagonal(pj - pk):
                vals.append(pj - pk)
    acc = 0
    for v in vals:
        acc = min(acc, v)
    return acc


if __name__ == '__main__':
    assert pentagonal(4) + pentagonal(7) == pentagonal(8)

