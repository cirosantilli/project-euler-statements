from itertools import combinations

SQUARE_PAIRS: list[tuple[int, int]] = [
    (0, 1), (0, 4), (0, 9), (1, 6), (2, 5), (3, 6), (4, 9), (6, 4), (8, 1),
]


def expand69(xs: list[int]) -> list[int]:
    out = list(xs)
    if 6 in out or 9 in out:
        for d in (6, 9):
            if d not in out:
                out.append(d)
    return out


def can_show(a: list[int], b: list[int], required_pairs: list[tuple[int, int]]) -> bool:
    aa, bb = expand69(a), expand69(b)
    return all((x in aa and y in bb) or (y in aa and x in bb) for x, y in required_pairs)


def choose_faces(xs: list[int], face_count: int) -> list[list[int]]:
    if face_count < 0 or face_count > len(xs):
        return []
    return [list(c) for c in combinations(xs, face_count)]


def naive(face_count: int, required_pairs: list[tuple[int, int]]) -> int:
    cubes = choose_faces(list(range(10)), face_count)
    pairs = 0
    for i, a in enumerate(cubes):
        for b in cubes[i:]:
            if can_show(a, b, required_pairs):
                pairs += 1
    return pairs


if __name__ == "__main__":
    assert can_show([0, 5, 6, 7, 8, 9], [1, 2, 3, 4, 8, 9], SQUARE_PAIRS)
    print(naive(6, SQUARE_PAIRS))

