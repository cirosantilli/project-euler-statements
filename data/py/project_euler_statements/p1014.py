from itertools import combinations
from math import comb


def solve(
    v: int, k: int, t: int, nights: tuple[str, ...], target: str
) -> str:
    """Enumerate every k-subset, then test target and intersection constraints."""
    counts = [0] * t
    for j in reversed(range(t)):
        numerator = comb(v - j, t - j)
        denominator = comb(k - j, t - j)
        if numerator % denominator:
            raise ValueError("Nonintegral Steiner system parameters")
        counts[j] = comb(k, j) * (numerator // denominator - 1)
        for i in range(j + 1, t):
            counts[j] -= comb(i, j) * counts[i]
    if min(counts) < 0:
        raise ValueError("Impossible Steiner system parameters")
    allowed = {i for i in range(t) if counts[i] > 0} | {k}
    known = [set(night) for night in nights]
    wanted = set(target)
    answers = []
    for members in combinations("ABCDEFGHIJKLMNOPQRSTUVWXYZ"[:v], k):
        candidate = set(members)
        if wanted <= candidate and all(
            len(candidate & night) in allowed for night in known
        ):
            answers.append("".join(members))
    if len(answers) != 1:
        raise ValueError("The intersection constraints do not force one block")
    return answers[0]


if __name__ == "__main__":
    assert solve(7, 3, 2, ("ABC", "BDF"), "EG") == "BEG"
