from itertools import permutations


def lex_le(a: list[int], b: list[int]) -> bool:
    if not a:
        return True
    if not b:
        return False
    return lex_le(a[1:], b[1:]) if a[0] == b[0] else a[0] <= b[0]


def naive(digits: list[int], idx: int) -> list[int]:
    ps = sorted((list(p) for p in permutations(digits)))
    return ps[idx - 1] if 0 <= idx - 1 < len(ps) else []


if __name__ == '__main__':
    assert naive([0, 1, 2], 1) == [0, 1, 2]
    assert naive([0, 1, 2], 6) == [2, 1, 0]

