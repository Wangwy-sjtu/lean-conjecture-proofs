"""Compare independent exact ordered draws against the hand formula for Levin's game."""

from collections import defaultdict
from fractions import Fraction
from math import comb


def ordered_draw_mass(s, lower, upper):
    """Run the stopping rule forward using the remaining count of each rank."""
    mass = defaultdict(Fraction)
    active = {(0, 0, 0): Fraction(1)}
    for draw in range(1, 3 * s + 1):
        following = defaultdict(Fraction)
        for previous, probability in active.items():
            for rank, used in enumerate(previous):
                if used == s:
                    continue
                updated = list(previous)
                updated[rank] += 1
                new = tuple(updated)
                chance = probability * Fraction(s - used, 3 * s - draw + 1)
                if max(new) > upper:
                    mass[draw] += chance
                elif min(new) < lower:
                    following[new] += chance
        active = following
        if not active:
            break
    return [mass[n] for n in range(3 * s + 1)]


def hand_mass(s, lower, upper, n):
    if not upper < n <= 2 * upper + lower:
        return Fraction(0)
    k = n - 1 - upper
    total = 0
    for i in range(upper + 1):
        j = k - i
        if 0 <= j <= upper and min(i, j) < lower:
            total += comb(s, i) * comb(s, j)
    return Fraction(comb(s - 1, upper) * total, comb(3 * s - 1, n - 1))


def check(max_s=9):
    cases = 0
    for s in range(2, max_s + 1):
        for upper in range(1, s):
            for lower in range(1, upper + 1):
                p = ordered_draw_mass(s, lower, upper)
                q = [hand_mass(s, lower, upper, n) for n in range(3 * s + 1)]
                assert p == q, (s, lower, upper)
                assert all(y * y >= x * z for x, y, z in zip(p, p[1:], p[2:]))
                assert [n for n, x in enumerate(p) if x] == list(
                    range(upper + 1, 2 * upper + lower + 1)
                )
                cases += 1
    print(f'{cases} complete parameter triples passed; exact sequential drawing for 2 <= s <= {max_s}.')
    sample = ordered_draw_mass(5, 2, 3)
    print('s=5, lower=2, upper=3:', ', '.join(f'p({n})={x}' for n, x in enumerate(sample) if x))


if __name__ == '__main__':
    check()
