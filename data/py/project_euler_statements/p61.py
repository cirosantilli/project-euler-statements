from __future__ import annotations

def p3(n: int) -> int:
    return n * (n + 1) // 2


def p4(n: int) -> int:
    return n * n


def p5(n: int) -> int:
    return n * (3 * n - 1) // 2


def p6(n: int) -> int:
    return n * (2 * n - 1)


def p7(n: int) -> int:
    return n * (5 * n - 3) // 2


def p8(n: int) -> int:
    return n * (3 * n - 2)


def polygonal(sides: int, index: int) -> int:
    """
    @formalsw: Returns
    """
    return index * ((sides - 2) * index - (sides - 4)) // 2


def last_two(n: int) -> int:
    return n % 100


def first_two(n: int) -> int:
    return n // 100


def is_cyclic_pair(a: int, b: int) -> bool:
    return last_two(a) == first_two(b)


def is_cyclic_list(xs: list[int]) -> bool:
    if not xs:
        return False
    return all(is_cyclic_pair(a, b) for a, b in zip(xs, xs[1:])) and is_cyclic_pair(xs[-1], xs[0])


def four_digit(sides: int) -> list[int]:
    values = []
    index = 1
    while True:
        value = polygonal(sides, index)
        if value >= 10000:
            break
        if value >= 1000:
            values.append(value)
        index += 1
    return values


def naive(max_sides: int = 8) -> int:
    """
    Enumerate every type order, scanning whole families for each next value.
    Fix the first type to triangular; every cycle has that rotation.

    @formalsw: Returns
    """
    if max_sides < 3:
        return 0
    families = {sides: four_digit(sides) for sides in range(3, max_sides + 1)}

    def extend(path: list[int], remaining: list[int]) -> int:
        if not remaining:
            if is_cyclic_pair(path[-1], path[0]):
                return sum(path)
            return 0
        best = 0
        for kind in remaining:
            unused = [other for other in remaining if other != kind]
            for value in families[kind]:
                if value in path:
                    continue
                if not is_cyclic_pair(path[-1], value):
                    continue
                best = max(best, extend(path + [value], unused))
        return best

    best = 0
    for start in families[3]:
        best = max(best, extend([start], list(range(4, max_sides + 1))))
    return best


def naive_default() -> int:
    return naive()


if __name__ == "__main__":
    assert not is_cyclic_list([])
    assert is_cyclic_list([5151])
    assert not is_cyclic_list([1234])
    assert is_cyclic_list([8128, 2882, 8281])
    assert is_cyclic_list([8256, 5625, 2512, 1281, 8128, 2882])
    assert naive(-1) == 0
    assert naive(2) == 0
    assert naive_default() == 28684
