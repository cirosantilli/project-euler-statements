from math import log


def score(p: tuple[int, int]) -> float:
    return p[1] * log(p[0])


def naive(pairs: list[tuple[int, int]]) -> int:
    indexed = list(enumerate(pairs, 1))
    if not indexed:
        return 0
    best_i, best_p = indexed[0]
    best_s = score(best_p)
    for i, p in indexed[1:]:
        s = score(p)
        if s > best_s:
            best_i, best_s = i, s
    return best_i


if __name__ == '__main__':
    assert 2 ** 11 < 3 ** 7

