from common import digits_le


def num_digits(n: int) -> int:
    return len(digits_le(n))


def naive(limit: int) -> int:
    acc = 0
    for n in range(limit + 1):
        for a in range(10):
            if a != 0 and num_digits(a ** n) == n:
                acc += 1
    return acc


if __name__ == '__main__':
    assert num_digits(7 ** 5) == 5
    assert num_digits(8 ** 9) == 9

