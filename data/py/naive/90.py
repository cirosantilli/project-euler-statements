from itertools import combinations

squares = [(0,1),(0,4),(0,9),(1,6),(2,5),(3,6),(4,9),(6,4),(8,1)]


def expand69(xs):
    out = list(xs)
    if 6 in out or 9 in out:
        for d in (6, 9):
            if d not in out:
                out.append(d)
    return out


def can_show(a, b) -> bool:
    aa, bb = expand69(a), expand69(b)
    return all((x in aa and y in bb) or (y in aa and x in bb) for x, y in squares)


def choose6(xs):
    return [list(c) for c in combinations(xs, 6)]


def naive() -> int:
    cubes = choose6(list(range(10)))
    pairs = 0
    for i, a in enumerate(cubes):
        for b in cubes[i:]:
            if can_show(a, b):
                pairs += 1
    return pairs


if __name__ == '__main__':
    assert can_show([0,5,6,7,8,9], [1,2,3,4,8,9])

