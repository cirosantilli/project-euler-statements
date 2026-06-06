coins = [1, 2, 5, 10, 20, 50, 100, 200]


def count_ways_bound(amt: int, cs: list[int]) -> int:
    if amt == 0:
        return 1
    if not cs:
        return 0
    c, rest = cs[0], cs[1:]
    if c == 0 or amt < c:
        return count_ways_bound(amt, rest)
    return count_ways_bound(amt - c, cs) + count_ways_bound(amt, rest)


def naive(amt: int) -> int:
    return count_ways_bound(amt, coins)


if __name__ == '__main__':
    assert 100 + 50 + 20 + 20 + 5 + 2 + 1 + 1 + 1 == 200

