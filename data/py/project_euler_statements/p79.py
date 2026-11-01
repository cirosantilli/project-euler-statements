from collections.abc import Iterable


def edges_from(s: str) -> list[tuple[str, str]]:
    return [(s[0], s[1]), (s[1], s[2]), (s[0], s[2])] if len(s) >= 3 else []


def erase_dups(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


def nodes(attempts: list[str]) -> list[str]:
    return erase_dups([c for s in attempts for c in s])


def edges(attempts: list[str]) -> list[tuple[str, str]]:
    return erase_dups([e for s in attempts for e in edges_from(s)])


def incoming(n: str, es: list[tuple[str, str]]) -> bool:
    return any(e[1] == n for e in es)


def remove_node(n: str, es: list[tuple[str, str]]) -> list[tuple[str, str]]:
    return [e for e in es if e[0] != n and e[1] != n]


def topo(ns: list[str], es: list[tuple[str, str]]) -> list[str]:
    ns = sorted(ns)
    out = []
    while ns:
        found = next((n for n in ns if not incoming(n, es)), None)
        if found is None:
            raise ValueError("Constraints contain a cycle; no valid passcode exists.")
        out.append(found)
        ns = [n for n in ns if n != found]
        es = remove_node(found, es)
    return out


def naive(attempts: Iterable[str]) -> str:
    """
    Find the least ordering of distinct digits by repeatedly scanning all remaining constraints.
    """
    checked: list[str] = []
    for attempt in attempts:
        if len(attempt) != 3 or not attempt.isdigit():
            raise ValueError(f"Invalid attempt: {attempt!r}")
        checked.append(attempt)
    return "".join(topo(nodes(checked), edges(checked)))
