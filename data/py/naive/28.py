def layer_sum(k: int) -> int:
    return 16 * k ** 2 + 4 * k + 4


def spiral_diag_sum(n: int) -> int:
    layers = (n - 1) // 2
    return sum(1 if k == 0 else layer_sum(k) for k in range(layers + 1))


def naive(n: int) -> int:
    return spiral_diag_sum(n)


if __name__ == '__main__':
    assert spiral_diag_sum(5) == 101

