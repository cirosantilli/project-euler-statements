from common import digits_le


def digit_sum(n: int) -> int:
    return sum(digits_le(n))


def naive(n: int) -> int:
    return digit_sum(2 ** n)


if __name__ == '__main__':
    assert naive(15) == 26

