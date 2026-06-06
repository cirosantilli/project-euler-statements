from common import digits_le


def digits_sorted(n: int) -> list[int]:
    return sorted(digits_le(n))


def same_digits(a: int, b: int) -> bool:
    return digits_sorted(a) == digits_sorted(b)


def has_permuted_multiples(n: int, x: int) -> bool:
    return n >= 2 and all(same_digits(x, (i + 2) * x) for i in range(n - 1))


def naive(n: int) -> int:
    x = 0
    while True:
        if has_permuted_multiples(n, x):
            return x
        x += 1


if __name__ == '__main__':
    assert same_digits(125874, 2 * 125874)

