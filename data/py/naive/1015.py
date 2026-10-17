from functools import cache


def solve(n: int, modulus: int = 10**9) -> int:
    """Enumerate all rows and solve the original game by minimax."""

    @cache
    def wins(blue: int, red: int, turn: int) -> bool:
        own = red if turn else blue
        occupied = blue | red
        for i in range(n):
            moves = []
            if own >> i & 1:
                moves.append(1 << i)
            if i + 1 < n:
                pair = 3 << i
                if occupied & pair == pair and own & pair:
                    moves.append(pair)
            for removed in moves:
                if not wins(blue & ~removed, red & ~removed, 1 - turn):
                    return True
        return False

    full = (1 << n) - 1
    count = 0
    for blue in range(1 << n):
        red = full ^ blue
        if not wins(blue, red, 0) and not wins(blue, red, 1):
            count += 1
    return count % modulus


if __name__ == "__main__":
    assert solve(0) == 1
    assert solve(6) == 8
