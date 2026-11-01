def get_col(matrix: list[list[int]], c: int) -> list[int]:
    return [row[c] if c < len(row) else 0 for row in matrix]


def add_lists(a: list[int], b: list[int]) -> list[int]:
    return [x + y for x, y in zip(a, b)] if len(a) == len(b) else []


def relax_down(cost: list[int], col: list[int]) -> list[int]:
    if len(cost) != len(col) or not cost:
        return []
    out = [cost[0]]
    prev = cost[0]
    for c, v in zip(cost[1:], col[1:]):
        cur = min(c, prev + v)
        out.append(cur)
        prev = cur
    return out


def relax_up(cost: list[int], col: list[int]) -> list[int]:
    return list(reversed(relax_down(list(reversed(cost)), list(reversed(col)))))


def min_path(matrix: list[list[int]]) -> int:
    if not matrix:
        return 0
    cols = [get_col(matrix, c) for c in range(len(matrix[0]))]
    if not cols:
        return 0
    final = cols[0]
    for col in cols[1:]:
        base = add_lists(final, col)
        final = relax_up(relax_down(base, col), col)
    return min(final) if final else 0


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
    assert min_path(sample) == 994

