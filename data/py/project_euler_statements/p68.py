from itertools import permutations


def ring_string(outer: list[int], inner: tuple[int, ...], start: int) -> str:
    n = len(inner)
    parts: list[str] = []
    for offset in range(n):
        index = (start + offset) % n
        parts.append(str(outer[index]) + str(inner[index]) + str(inner[(index + 1) % n]))
    return "".join(parts)


def naive(n: int = 5, digits: int = 16) -> str:
    """
    @formalsw: Returns
    """
    if n < 3 or digits < 3 * n:
        return ""
    best = ""
    for values in permutations(list(range(1, 2 * n + 1))):
        outer = list(values[:n])
        inner = values[n:]
        if outer[0] != min(outer):
            continue
        target = outer[0] + inner[0] + inner[1]
        magic = True
        for index in range(1, n):
            if outer[index] + inner[index] + inner[(index + 1) % n] != target:
                magic = False
                break
        if not magic:
            continue
        text = ring_string(outer, inner, 0)
        if len(text) == digits and text > best:
            best = text
    return best


def max_string_3_gon() -> int:
    return int(naive(3, 9) or "0")


def max_string_5_gon() -> int:
    return int(naive() or "0")


if __name__ == "__main__":
    assert naive(3, 9) == "432621513"
