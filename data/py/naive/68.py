from itertools import permutations
from common import digits_le


def num_digits(n: int) -> int:
    return len(digits_le(n))


def concat_nat(a: int, b: int) -> int:
    return a * 10 ** num_digits(b) + b


def concat_list(xs: list[int]) -> int:
    acc = 0
    for x in xs:
        acc = concat_nat(acc, x)
    return acc


def max_string_3_gon() -> int:
    vals = []
    for p in permutations([1, 2, 3, 4, 5, 6]):
        a, b, c, d, e, f = p
        s1, s2, s3 = a + b + c, d + c + e, f + e + b
        if s1 == s2 == s3 and a <= d and a <= f:
            vals.append(concat_list([a, b, c, d, c, e, f, e, b]))
    return max(vals) if vals else 0


def max_string_5_gon() -> int:
    vals = []
    for p in permutations([1,2,3,4,5,6,7,8,9,10]):
        o1,o2,o3,o4,o5,i1,i2,i3,i4,i5 = p
        sums = [o1+i1+i2, o2+i2+i3, o3+i3+i4, o4+i4+i5, o5+i5+i1]
        if len(set(sums)) == 1 and o1 <= o2 and o1 <= o3 and o1 <= o4 and o1 <= o5:
            v = concat_list([o1,i1,i2,o2,i2,i3,o3,i3,i4,o4,i4,i5,o5,i5,i1])
            if num_digits(v) == 16:
                vals.append(v)
    return max(vals) if vals else 0


def naive() -> int:
    return max_string_5_gon()


if __name__ == '__main__':
    assert max_string_3_gon() == 432621513

