def dims(m):
    return (len(m), len(m[0]) if m else 0)


def get_d2(m, r, c):
    return m[r][c] if 0 <= r < len(m) and 0 <= c < len(m[r]) else 0


def big_val(m):
    return sum(sum(row) for row in m) + 1


def init_dist(m):
    rows, cols = dims(m)
    big = big_val(m)
    return [[get_d2(m, 0, 0) if r == 0 and c == 0 else big for c in range(cols)] for r in range(rows)]


def neighbors(r, c, rows, cols):
    return [(rr, cc) for rr, cc in [(r + 1, c), (r, c + 1), (r, c - 1), (r - 1, c)] if rr >= 0 and cc >= 0 and rr < rows and cc < cols]


def relax_step(m, dist):
    rows, cols = dims(m)
    return [[min(get_d2(dist, r, c), get_d2(m, r, c) + min([get_d2(dist, rr, cc) for rr, cc in neighbors(r, c, rows, cols)] + [get_d2(dist, r, c)])) for c in range(cols)] for r in range(rows)]


def iterate(m, dist):
    rows, cols = dims(m)
    for _ in range(rows * cols):
        dist = relax_step(m, dist)
    return dist


small_matrix = [[131,673,234,103,18],[201,96,342,965,150],[630,803,746,422,111],[537,699,497,121,956],[805,732,524,37,331]]


def min_path(m):
    rows, cols = dims(m)
    return get_d2(iterate(m, init_dist(m)), rows - 1, cols - 1)


def naive(m):
    return min_path(m)


if __name__ == '__main__':
    assert min_path(small_matrix) == 2297

