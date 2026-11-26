"""Exact checks for the four-rank Band or Bump game, using two independent calculations."""

from collections import defaultdict
from fractions import Fraction
from math import comb


def sequential_bumps(s, lower, upper):
    """Draw from the remaining labelled cards and stop on the first band or bump."""
    bumps = [Fraction(0) for _ in range(4 * s + 1)]
    active = {(0, 0, 0, 0): Fraction(1)}
    for n in range(1, 4 * s + 1):
        following = defaultdict(Fraction)
        for counts, old_probability in active.items():
            for rank, used in enumerate(counts):
                if used == s:
                    continue
                new = list(counts)
                new[rank] += 1
                probability = old_probability * Fraction(s - used, 4 * s - n + 1)
                if max(new) > upper:
                    bumps[n] += probability
                elif min(new) < lower:
                    following[tuple(new)] += probability
        active = following
        if not active:
            break
    return bumps


def coefficients(s, first, second, third):
    p = [0] * (sum([first[-1], second[-1], third[-1]]) + 1)
    for i in first:
        for j in second:
            for k in third:
                p[i + j + k] += comb(s, i) * comb(s, j) * comb(s, k)
    return p


def compare(s, lower, upper):
    p = sequential_bumps(s, lower, upper)
    full = range(0, upper + 1)
    low = range(0, lower)
    high = range(lower, upper + 1)
    full_table = coefficients(s, full, full, full)
    high_table = coefficients(s, high, high, high)
    mixed_table = coefficients(s, low, full, high)
    low_table = coefficients(s, low, low, low)

    def get(a, i):
        return a[i] if 0 <= i < len(a) else 0

    for n, v in enumerate(p):
        k = n - 1 - upper
        a = get(full_table, k) - get(high_table, k)
        b = 3 * get(mixed_table, k) + get(low_table, k)
        assert a == b
        expected = Fraction(comb(s - 1, upper) * a, comb(4 * s - 1, n - 1)) if n else 0
        assert expected == v, (s, lower, upper, n)
    assert all(y * y >= x * z for x, y, z in zip(p, p[1:], p[2:]))
    assert [i for i, x in enumerate(p) if x] == list(range(upper + 1, 3 * upper + lower + 1))
    return p


if __name__ == '__main__':
    counter = 0
    for s in range(2, 10):
        for u in range(1, s):
            for l in range(1, u + 1):
                compare(s, l, u)
                counter += 1
    print(f'{counter} complete parameter triples and every draw time passed for 2 <= s <= 9.')
    table1 = compare(13, 5, 8)
    print(f'Levin Table 1 (s=13, l=5, u=8), exact total bump probability: {sum(table1)}')
    for n in (9, 24, 29):
        print(f'p({n}) = {table1[n]} = {float(table1[n]):.12f}')
