def grid_val(grid: list[list[int]], r: int, c: int) -> int:
    return grid[r][c] if 0 <= r < len(grid) and 0 <= c < len(grid[r]) else 0


def prod_right_n(grid, r, c, n):
    acc = 1
    for i in range(n):
        acc *= grid_val(grid, r, c + i)
    return acc


def prod_down_n(grid, r, c, n):
    acc = 1
    for i in range(n):
        acc *= grid_val(grid, r + i, c)
    return acc


def prod_diag_right_n(grid, r, c, n):
    acc = 1
    for i in range(n):
        acc *= grid_val(grid, r + i, c + i)
    return acc


def prod_diag_left_n(grid, r, c, n):
    acc = 1
    for i in range(n):
        acc *= grid_val(grid, r + i, c - i)
    return acc


def naive(grid: list[list[int]], n: int) -> int:
    products = []
    products += [prod_right_n(grid, r, c, n) for r in range(20) for c in range(21 - n)]
    products += [prod_down_n(grid, r, c, n) for r in range(21 - n) for c in range(20)]
    products += [prod_diag_right_n(grid, r, c, n) for r in range(21 - n) for c in range(21 - n)]
    products += [prod_diag_left_n(grid, r, c + n - 1, n) for r in range(21 - n) for c in range(21 - n)]
    return max(products) if products else 0

