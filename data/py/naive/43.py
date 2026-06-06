from itertools import permutations
from common import digits_be, of_digits_be


def sub_num(ds: list[int], i: int) -> int:
    return of_digits_be(ds[i:i + 3])


def has_property(ds: list[int]) -> bool:
    return (len(ds) == 10 and len(set(ds)) == 10 and sub_num(ds, 1) % 2 == 0 and
            sub_num(ds, 2) % 3 == 0 and sub_num(ds, 3) % 5 == 0 and
            sub_num(ds, 4) % 7 == 0 and sub_num(ds, 5) % 11 == 0 and
            sub_num(ds, 6) % 13 == 0 and sub_num(ds, 7) % 17 == 0)


def naive() -> int:
    return sum(of_digits_be(list(p)) for p in permutations(range(10)) if has_property(list(p)))


if __name__ == '__main__':
    assert has_property(digits_be(1406357289))

