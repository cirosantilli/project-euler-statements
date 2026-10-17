def row_step(prev: list[int], row: list[int]) -> list[int]:
    if not prev and not row:
        return []
    if not prev or not row:
        return []
    first = row[0] + prev[0]
    out = [first]
    left = first
    for p, x in zip(prev[1:], row[1:]):
        cur = x + min(p, left)
        out.append(cur)
        left = cur
    return out


small_matrix = [[131,673,234,103,18],[201,96,342,965,150],[630,803,746,422,111],[537,699,497,121,956],[805,732,524,37,331]]


def min_path(m: list[list[int]]) -> int:
    if not m:
        return 0
    init = []
    for x in m[0]:
        init.append(x + (init[-1] if init else 0))
    final = init
    for row in m[1:]:
        final = row_step(final, row)
    return final[-1] if final else 0


def naive(m: list[list[int]]) -> int:
    return min_path(m)


if __name__ == '__main__':
    assert min_path(small_matrix) == 2427

