from .common import digits_le, is_prime


def digits_sorted(n: int) -> list[int]:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sorted(digits_le(n))


def is_permutation(a: int, b: int) -> bool:
    """
    @formalsw: Requires(a >= 0 and b >= 0)
    @formalsw: Returns
    """
    return digits_sorted(a) == digits_sorted(b)


def seq_from(a: int, d: int, length: int) -> list[int]:
    """
    @formalsw: Returns
    """
    return [a + i * d for i in range(length)]


def naive(n: int, seqlen: int) -> list[list[int]]:
    if n == 0 or seqlen < 2:
        return []
    lower, upper = 10 ** (n - 1), 10 ** n
    out = []
    for a in range(upper):
        for d in range(upper):
            s = seq_from(a, d, seqlen)
            if lower <= a and d > 0 and s[-1] < upper and all(is_prime(x) for x in s) and all(is_permutation(s[0], y) for y in s[1:]):
                out.append(s)
    return out


def naive_default() -> int:
    """
    Select the first four-digit triple other than the given example and concatenate it.
    """
    for seq in naive(4, 3):
        if seq != [1487, 4817, 8147]:
            return seq[0] * 10 ** 8 + seq[1] * 10 ** 4 + seq[2]
    return 0


if __name__ == '__main__':
    assert is_prime(1487)
    assert is_prime(4817)
    assert is_prime(8147)
    assert is_permutation(1487, 4817)
    assert is_permutation(4817, 8147)

