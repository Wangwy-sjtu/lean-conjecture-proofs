"""Exact sequential simulation and independent occupancy-coefficient check for Band or Bump."""

from collections import defaultdict
from fractions import Fraction
from math import comb


def probabilities_from_draws(m, s, lo, up):
    """Forward recurrence on histograms: coordinate i counts the ranks seen i times."""
    mass = [Fraction(0) for _ in range(m * s + 1)]
    active = {(m,) + (0,) * s: Fraction(1)}
    for n in range(1, m * s + 1):
        next_layer = defaultdict(Fraction)
        for histogram, chance in active.items():
            for i in range(s):
                choices = histogram[i] * (s - i)
                if not choices:
                    continue
                updated = list(histogram)
                updated[i] -= 1
                updated[i + 1] += 1
                probability = chance * Fraction(choices, m * s - n + 1)
                if i + 1 > up:
                    mass[n] += probability
                elif sum(updated[:lo]) > 0:
                    next_layer[tuple(updated)] += probability
        active = next_layer
        if not active:
            break
    return mass


def product(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def power(p, n):
    value = [1]
    for _ in range(n):
        value = product(value, p)
    return value


def probabilities_from_hands(m, s, lo, up):
    mass = [Fraction(0) for _ in range(m * s + 1)]
    if up == 0:
        mass[1] = Fraction(1)
        return mass
    if lo == 0 or up == s or m == 1:
        return mass
    f = [comb(s, i) for i in range(up + 1)]
    g = [0] * lo + f[lo:]
    all_capped = power(f, m - 1)
    all_high = power(g, m - 1)
    missing = [x - y for x, y in zip(all_capped, all_high)]
    T = (m - 1) * s
    for k, a in enumerate(missing):
        n = up + k + 1
        mass[n] = Fraction(comb(s - 1, up) * a, comb(m * s - 1, n - 1))
        if 0 < k < len(missing) - 1:
            lhs = a * a * k * (T - k)
            rhs = missing[k - 1] * missing[k + 1] * (k + 1) * (T - k + 1)
            assert lhs >= rhs, ('normalized missing count', m, s, lo, up, k)
    return mass


def check(m, s, lo, up):
    a = probabilities_from_draws(m, s, lo, up)
    b = probabilities_from_hands(m, s, lo, up)
    assert a == b, ('stopping probability', m, s, lo, up)
    assert all(y * y >= x * z for x, y, z in zip(a, a[1:], a[2:]))
    if up == 0:
        support = [1]
    elif lo == 0 or up == s or m == 1:
        support = []
    else:
        support = list(range(up + 1, (m - 1) * up + lo + 1))
    assert [i for i, x in enumerate(a) if x] == support
    return sum(a)


if __name__ == '__main__':
    cases = 0
    for m in range(1, 10):
        for s in range(1, 8):
            for up in range(0, s + 1):
                for lo in range(0, up + 1):
                    check(m, s, lo, up)
                    cases += 1
    print(f'{cases} full parameter quadruples passed for 1 <= m <= 9, 1 <= s <= 7.')
    for m, s, lo, up in [(4, 13, 5, 8), (13, 4, 1, 3), (24, 3, 1, 2), (2, 40, 17, 21)]:
        p = check(m, s, lo, up)
        print(f'm={m}, s={s}, l={lo}, u={up}: total bump probability {p} = {float(p):.12f}')
