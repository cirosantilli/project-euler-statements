def is_right(a: int, b: int, c: int, d: int) -> bool:
    dx = c - a if c >= a else a - c
    dy = d - b if d >= b else b - d
    dot1 = a * a + b * b
    dot2 = dx * dx + dy * dy
    dot3 = c * c + d * d
    return dot1 + dot2 == dot3 or dot1 + dot3 == dot2 or dot2 + dot3 == dot1


def naive(limit: int) -> int:
    acc = 0
    for x1 in range(limit + 1):
     for y1 in range(limit + 1):
      for x2 in range(limit + 1):
       for y2 in range(limit + 1):
        if (x1 == 0 and y1 == 0) or (x2 == 0 and y2 == 0) or (x1 == x2 and y1 == y2):
            continue
        if is_right(x1, y1, x2, y2):
            acc += 1
    return acc // 2


if __name__ == '__main__':
    assert naive(2) == 14

