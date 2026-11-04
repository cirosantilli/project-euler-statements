def dims(matrix: list[list[int]]) -> tuple[int, int]:
    return (len(matrix), len(matrix[0]) if matrix else 0)


def get_d2(matrix: list[list[int]], r: int, c: int) -> int:
    return matrix[r][c] if 0 <= r < len(matrix) and 0 <= c < len(matrix[r]) else 0


def big_val(matrix: list[list[int]]) -> int:
    return sum(sum(row) for row in matrix) + 1


def init_dist(matrix: list[list[int]]) -> list[list[int]]:
    rows, cols = dims(matrix)
    big = big_val(matrix)
    return [
        [get_d2(matrix, 0, 0) if r == 0 and c == 0 else big for c in range(cols)]
        for r in range(rows)
    ]


def neighbors(r: int, c: int, rows: int, cols: int) -> list[tuple[int, int]]:
    return [
        (rr, cc)
        for rr, cc in [(r + 1, c), (r, c + 1), (r, c - 1), (r - 1, c)]
        if rr >= 0 and cc >= 0 and rr < rows and cc < cols
    ]


def relax_step(matrix: list[list[int]], dist: list[list[int]]) -> list[list[int]]:
    rows, cols = dims(matrix)
    return [
        [
            min(
                get_d2(dist, r, c),
                get_d2(matrix, r, c) + min(
                    [get_d2(dist, rr, cc) for rr, cc in neighbors(r, c, rows, cols)]
                    + [get_d2(dist, r, c)]
                ),
            )
            for c in range(cols)
        ]
        for r in range(rows)
    ]


def iterate(matrix: list[list[int]], dist: list[list[int]]) -> list[list[int]]:
    rows, cols = dims(matrix)
    for _ in range(rows * cols):
        dist = relax_step(matrix, dist)
    return dist


def min_path(matrix: list[list[int]]) -> int:
    rows, cols = dims(matrix)
    return get_d2(iterate(matrix, init_dist(matrix)), rows - 1, cols - 1)


def is_rectangular(matrix: list[list[int]]) -> bool:
    if not matrix:
        return True
    width = len(matrix[0])
    for row in matrix:
        if len(row) != width:
            return False
    return True


def has_nonnegative_entries(matrix: list[list[int]]) -> bool:
    for row in matrix:
        for value in row:
            if value < 0:
                return False
    return True


def naive(matrix: list[list[int]]) -> int:
    """
    @formalsw: Requires(is_rectangular(matrix))
    @formalsw: Requires(has_nonnegative_entries(matrix))
    @formalsw: Returns
    """
    return min_path(matrix)


if __name__ == '__main__':
    sample = [
        [131, 673, 234, 103, 18],
        [201, 96, 342, 965, 150],
        [630, 803, 746, 422, 111],
        [537, 699, 497, 121, 956],
        [805, 732, 524, 37, 331],
    ]
    assert naive(sample) == 2297
