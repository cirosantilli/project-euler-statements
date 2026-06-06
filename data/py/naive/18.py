Triangle = list[list[int]]


def max_row(row: list[int], below: list[int]) -> list[int]:
    if not row or len(below) < 2:
        return []
    return [x + max(y, z) for x, y, z in zip(row, below, below[1:])]


small_triangle_t = [[3], [7, 4], [2, 4, 6], [8, 5, 9, 3]]


def naive(tri: Triangle) -> int:
    rows = list(reversed(tri))
    if not rows:
        return 0
    acc = rows[0]
    for row in rows[1:]:
        acc = max_row(row, acc)
    return acc[0] if acc else 0


if __name__ == '__main__':
    assert naive(small_triangle_t) == 23

