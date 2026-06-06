def row_ok(row: list[int]) -> bool:
    vals = [x for x in row if x != 0]
    return len(set(vals)) == len(vals)


def grid_ok(g: list[list[int]]) -> bool:
    return all(row_ok(row) for row in g)


def naive(grids: list[list[list[int]]]) -> int:
    return len(grids)


if __name__ == '__main__':
    assert row_ok([1,2,3,4,5,6,7,8,9])

