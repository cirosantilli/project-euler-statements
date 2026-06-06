rank_values = {'2':2,'3':3,'4':4,'5':5,'6':6,'7':7,'8':8,'9':9,'T':10,'J':11,'Q':12,'K':13,'A':14}


def rank_value(rank) -> int:
    return rank if isinstance(rank, int) else rank_values[rank]


def hand_ranks(hand):
    return [rank_value(c[0]) for c in hand]


def hand_suits(hand):
    return [c[1] for c in hand]


def is_flush(hand) -> bool:
    suits = hand_suits(hand)
    return bool(suits) and all(s == suits[0] for s in suits[1:])


def sorted_ranks(rs):
    return sorted(rs)


def is_straight(rs) -> bool:
    rs = sorted_ranks(rs)
    if rs == [2, 3, 4, 5, 14]:
        return True
    return bool(rs) and all(r == rs[0] + i for i, r in enumerate(rs))


def straight_high(rs) -> int:
    rs = sorted_ranks(rs)
    return 5 if rs == [2, 3, 4, 5, 14] else (rs[-1] if rs else 0)


def rank_counts(rs):
    vals = []
    for r in rs:
        if r not in vals:
            vals.append(r)
    return [(rs.count(v), v) for v in vals]


def sort_counts(cs):
    return sorted(cs, key=lambda p: (-p[0], -p[1]))


def counts_key(rs):
    out = []
    for count, value in sort_counts(rank_counts(rs)):
        out += [value] * count
    return out


def hand_score(hand):
    rs = hand_ranks(hand)
    flush = is_flush(hand)
    straight = is_straight(rs)
    sorted_rs = sorted_ranks(rs)
    key_counts = counts_key(rs)
    if straight and flush:
        return (9, []) if sorted_rs == [10, 11, 12, 13, 14] else (8, [straight_high(rs)])
    sc = sort_counts(rank_counts(rs))
    if sc and sc[0][0] == 4:
        return (7, key_counts)
    if len(sc) >= 2 and sc[0][0] == 3 and sc[1][0] == 2:
        return (6, key_counts)
    if flush:
        return (5, list(reversed(sorted_rs)))
    if straight:
        return (4, [straight_high(rs)])
    if sc and sc[0][0] == 3:
        return (3, key_counts)
    if len(sc) >= 2 and sc[0][0] == 2 and sc[1][0] == 2:
        return (2, key_counts)
    if sc and sc[0][0] == 2:
        return (1, key_counts)
    return (0, list(reversed(sorted_rs)))


def lex_gt(a, b) -> bool:
    if not a or not b:
        return False
    return lex_gt(a[1:], b[1:]) if a[0] == b[0] else a[0] > b[0]


def beats(h1, h2) -> bool:
    s1, s2 = hand_score(h1), hand_score(h2)
    return lex_gt(s1[1], s2[1]) if s1[0] == s2[0] else s1[0] > s2[0]


def naive(hands) -> int:
    return sum(1 for h1, h2 in hands if beats(h1, h2))

