def sum_squares(n: int) -> int:
    return sum(i * i for i in range(1, n + 1))


def square_sum(n: int) -> int:
    return sum(range(1, n + 1)) ** 2


def naive(n: int) -> int:
    return square_sum(n) - sum_squares(n)


if __name__ == '__main__':
    assert sum_squares(10) == 385
    assert square_sum(10) == 3025
    assert naive(10) == 2640

