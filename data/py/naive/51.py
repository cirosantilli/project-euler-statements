from common import digits_le, of_digits_le, is_prime, sublists


def replace_at(digits: list[int], idxs: list[int], d: int) -> list[int]:
    return [d if i in idxs else x for i, x in enumerate(digits)]


def family_numbers(n: int, idxs: list[int]) -> list[int]:
    digits = digits_le(n)
    length = len(digits)
    out = []
    for d in range(10):
        m = of_digits_le(replace_at(digits, idxs, d))
        if len(digits_le(m)) == length:
            out.append(m)
    return out


def prime_family_size(n: int, idxs: list[int]) -> int:
    return sum(1 for m in family_numbers(n, idxs) if is_prime(m))


def has_prime_family(k: int, n: int) -> bool:
    return is_prime(n) and any(prime_family_size(n, s) >= k for s in sublists(list(range(len(digits_le(n))))) if s)


def naive(k: int) -> int:
    n = 0
    while True:
        if has_prime_family(k, n):
            return n
        n += 1


if __name__ == '__main__':
    assert prime_family_size(13, [1]) == 6
    assert prime_family_size(56003, [1, 2]) == 7

