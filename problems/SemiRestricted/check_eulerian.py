"""Check the proposed public mixed strategy against every possible next card."""

from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import comb


@cache
def potential(t, s):
    return Fraction(sum(comb(t, j) * abs(s + 2 * j - t) for j in range(t + 1)), 2 ** t)


def eulerian_graphs(d):
    pairs = list(combinations(range(d), 2))
    for directions in product((-1, 0, 1), repeat=len(pairs)):
        payoff = [[0] * d for _ in range(d)]
        for (i, j), sign in zip(pairs, directions):
            payoff[i][j], payoff[j][i] = sign, -sign
        if any(directions) and all(sum(row) == 0 for row in payoff):
            yield payoff


def disjoint_cycles(*lengths):
    d = sum(lengths)
    payoff = [[0] * d for _ in range(d)]
    start = 0
    for length in lengths:
        for j in range(length):
            a, b = start + j, start + (j + 1) % length
            payoff[a][b], payoff[b][a] = 1, -1
        start += length
    return payoff


def check(payoff, n):
    d = len(payoff)
    checks = roots = 0
    for a, f in enumerate(payoff):
        if not any(f):
            continue
        active = n * sum(map(abs, f))
        guarantee = potential(active, 0) / d
        assert 4 * d ** 2 * guarantee ** 2 >= n
        roots += 1
        for r in product(range(n + 1), repeat=d):
            t = sum(abs(y) * k for y, k in zip(f, r))
            s = -sum(y * k for y, k in zip(f, r))
            z = (potential(t - 1, s - 1) - potential(t - 1, s + 1)) / 2 if t else 0
            weights = [Fraction(d - z + (d * z if b == a else 0), d ** 2) for b in range(d)]
            assert min(weights) >= 0 and sum(weights) == 1
            for u, count in enumerate(r):
                if not count:
                    continue
                y = f[u]
                direct = sum(q * row[u] for q, row in zip(weights, payoff))
                after = potential(t - abs(y), s + y)
                assert direct + after / d == potential(t, s) / d
                checks += 1
    return roots, checks


def main():
    graphs = roots = steps = 0
    for d, quotas in [(3, (1, 2, 3)), (4, (1, 2)), (5, (1,))]:
        for graph in eulerian_graphs(d):
            graphs += 1
            for n in quotas:
                r, s = check(graph, n)
                roots += r
                steps += s
    for lengths in [(6,), (3, 3), (3, 4), (4, 4)]:
        r, s = check(disjoint_cycles(*lengths), 1)
        roots += r
        steps += s
    for t in range(101):
        assert 4 * potential(t, 0) ** 2 >= t
    print(f"All {graphs} nonempty labelled Eulerian oriented graphs on 3–5 vertices.")
    print("Four additional even or disconnected cycle examples on 6–8 vertices.")
    print(f"Initial guarantees: {roots}. Exact next-card identities: {steps}.")
    print("The walk lower bound agrees with binomial summation for all t = 0,...,100.")


if __name__ == "__main__":
    main()
