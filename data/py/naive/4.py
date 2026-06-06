from common import digits_le


def is_palindrome(n: int) -> bool:
    ds = digits_le(n)
    return ds == list(reversed(ds))


def digit_lower(digits: int) -> int:
    return 0 if digits == 0 else 10 ** (digits - 1)


def digit_upper(digits: int) -> int:
    return 10 ** digits - 1


def naive(digits: int) -> int:
    lo = digit_lower(digits)
    hi = digit_upper(digits)
    vals = [a * b for a in range(lo, hi + 1) for b in range(lo, hi + 1) if is_palindrome(a * b)]
    return max(vals) if vals else 0


if __name__ == '__main__':
    assert naive(2) == 9009

