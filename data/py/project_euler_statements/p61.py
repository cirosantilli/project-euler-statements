def p3(n): return n * (n + 1) // 2

def p4(n): return n * n

def p5(n): return n * (3 * n - 1) // 2

def p6(n): return n * (2 * n - 1)

def p7(n): return n * (5 * n - 3) // 2

def p8(n): return n * (3 * n - 2)

def last_two(n): return n % 100

def first_two(n): return n // 100


def is_cyclic_pair(a, b): return last_two(a) == first_two(b)


def is_cyclic_list(xs):
    if len(xs) < 2:
        return False
    return all(is_cyclic_pair(a, b) for a, b in zip(xs, xs[1:])) and is_cyclic_pair(xs[-1], xs[0])


def four_digit(f, limit):
    return [f(i) for i in range(limit + 1) if 1000 <= f(i) < 10000]


def naive(limit: int) -> int:
    sets = [four_digit(f, limit) for f in [p3, p4, p5, p6, p7, p8]]
    best = 0
    for a in sets[0]:
      for b in sets[1]:
       for c in sets[2]:
        for d in sets[3]:
         for e in sets[4]:
          for f in sets[5]:
           xs = [a, b, c, d, e, f]
           if is_cyclic_list(xs):
            best = max(best, sum(xs))
    return best


if __name__ == '__main__':
    assert is_cyclic_list([8128, 2882, 8281])

