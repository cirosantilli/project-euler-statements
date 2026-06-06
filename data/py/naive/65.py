from common import digits_le


def coeff_e(k: int) -> int:
    return 2 if k == 0 else (2 * (k // 3 + 1) if k % 3 == 2 else 1)


def coeffs(n: int) -> list[int]:
    return [coeff_e(k) for k in range(n)]


def convergent_num(n: int) -> int:
    p0, p1 = 0, 1
    for a in coeffs(n):
        p0, p1 = p1, a * p1 + p0
    return p1


def digit_sum(n: int) -> int:
    return sum(digits_le(n))


def naive(n: int) -> int:
    return digit_sum(convergent_num(n))


if __name__ == '__main__':
    assert digit_sum(convergent_num(10)) == 17

