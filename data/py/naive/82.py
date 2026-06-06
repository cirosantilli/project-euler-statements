def get_col(m, c):
    return [row[c] if c < len(row) else 0 for row in m]


def add_lists(a, b):
    return [x + y for x, y in zip(a, b)] if len(a) == len(b) else []


def relax_down(cost, col):
    if len(cost) != len(col) or not cost:
        return []
    out = [cost[0]]
    prev = cost[0]
    for c, v in zip(cost[1:], col[1:]):
        cur = min(c, prev + v)
        out.append(cur)
        prev = cur
    return out


def relax_up(cost, col):
    return list(reversed(relax_down(list(reversed(cost)), list(reversed(col)))))


small_matrix = [[131,673,234,103,18],[201,96,342,965,150],[630,803,746,422,111],[537,699,497,121,956],[805,732,524,37,331]]


def min_path(m):
    if not m:
        return 0
    cols = [get_col(m, c) for c in range(len(m[0]))]
    if not cols:
        return 0
    final = cols[0]
    for col in cols[1:]:
        base = add_lists(final, col)
        final = relax_up(relax_down(base, col), col)
    return min(final) if final else 0


def naive(m):
    return min_path(m)


if __name__ == '__main__':
    assert min_path(small_matrix) == 994

