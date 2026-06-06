from common import digits_le


def is_palindrome_base(b: int, n: int) -> bool:
    ds = digits_le(n, b)
    return ds == list(reversed(ds))


def is_double_palindrome(n: int) -> bool:
    return is_palindrome_base(10, n) and is_palindrome_base(2, n)


def naive(limit: int) -> int:
    return sum(n for n in range(limit) if is_double_palindrome(n))


if __name__ == '__main__':
    assert is_double_palindrome(585)

