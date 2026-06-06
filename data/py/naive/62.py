from common import digits_le


def digits_key(n: int) -> list[int]:
    return sorted(digits_le(n))


def cube_perm_count(limit: int, n: int) -> int:
    key = digits_key(n ** 3)
    return sum(1 for i in range(limit + 1) if digits_key(i ** 3) == key)


def naive(limit: int, target: int) -> int:
    for n in range(limit + 1):
        if cube_perm_count(limit, n) == target:
            return n ** 3
    return 0


if __name__ == '__main__':
    assert cube_perm_count(500, 345) == 3

