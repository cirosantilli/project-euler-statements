from common import digits_le, of_digits_le


def reverse_digits(n: int) -> int:
    return of_digits_le(list(reversed(digits_le(n))))


def is_palindrome(n: int) -> bool:
    ds = digits_le(n)
    return ds == list(reversed(ds))


def reverse_add(n: int) -> int:
    return n + reverse_digits(n)


def iterate(f, k: int, n: int) -> int:
    for _ in range(k):
        n = f(n)
    return n


def pal_at(n: int, k: int) -> bool:
    return is_palindrome(iterate(reverse_add, k, n))


def reaches_palindrome(n: int, max_iters: int) -> bool:
    return any(pal_at(n, k) for k in range(max_iters))


def is_lychrel(n: int, max_iters: int) -> bool:
    return not reaches_palindrome(n, max_iters)


def naive(n: int, max_iters: int) -> int:
    return sum(1 for x in range(n) if is_lychrel(x, max_iters))


if __name__ == '__main__':
    assert pal_at(47, 1)
    assert pal_at(349, 3)

