"""Recompute killed-chain hitting means and the two energy remainders over Q."""

from fractions import Fraction as Q
from itertools import combinations


def solve(rows):
    """Exact Gaussian elimination for an augmented matrix with a unique solution."""
    a = [[Q(entry) for entry in row] for row in rows]
    n = len(a)
    for col in range(n):
        pivot = next(i for i in range(col, n) if a[i][col])
        a[pivot], a[col] = a[col], a[pivot]
        factor = a[col][col]
        a[col] = [x / factor for x in a[col]]
        for i in range(n):
            if i == col or not a[i][col]:
                continue
            factor = a[i][col]
            a[i] = [x - factor*y for x, y in zip(a[i], a[col])]
    return [row[-1] for row in a]


def one_target(adj, t):
    n = len(adj)
    vertices = list(range(n))
    volume = sum(map(len, adj))
    srw_matrix = []
    for i in vertices:
        row = [0] * (n+1)
        if i == t:
            row[i] = 1
        else:
            row[i] = row[-1] = len(adj[i])
            for j in adj[i]:
                row[j] -= 1
        srw_matrix.append(row)
    simple = solve(srw_matrix)

    edges = [(i, j) for i in vertices for j in adj[i] if j != t]
    index = {edge: k for k, edge in enumerate(edges)}
    nb_matrix = []
    for prev, i in edges:
        row = [0] * (len(edges)+1)
        row[index[prev, i]] = row[-1] = len(adj[i])-1
        for j in adj[i]:
            if j != prev and j != t:
                row[index[i, j]] -= 1
        nb_matrix.append(row)
    after = dict(zip(edges, solve(nb_matrix)))
    fresh = [
        0 if i == t else 1 + sum(after.get((i, j), 0) for j in adj[i]) / len(adj[i])
        for i in vertices
    ]
    strict_difference = sum(len(adj[i])*(simple[i]-fresh[i]) for i in vertices)
    c = [0 if i == t else Q(1, len(adj[i])) for i in vertices]
    discrepancy = 0
    variation = 0
    for i in vertices:
        for j in adj[i]:
            ordinary = simple[i] - simple[j]
            current = after.get((j, i), 0) - after.get((i, j), 0)
            discrepancy += (1-c[i]-c[j])*(ordinary-current)**2
            variation += c[i]*(ordinary-1)**2
    assert discrepancy >= 0 and variation > 0
    assert 2*strict_difference == discrepancy + 2*variation
    return strict_difference / volume


def graphs_up_to_five():
    for n in range(3, 6):
        edges = list(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            adj = [set() for _ in range(n)]
            for b, (i, j) in enumerate(edges):
                if mask & (1 << b):
                    adj[i].add(j)
                    adj[j].add(i)
            if all(len(a) >= 2 for a in adj):
                yield adj


def main():
    graphs = 0
    targets = 0
    for adj in graphs_up_to_five():
        for t in range(len(adj)):
            assert one_target(adj, t) > 0
            targets += 1
        graphs += 1
    print(f"{graphs} labelled graphs of orders 3 through 5, {targets} fixed-target comparisons.")

    for n in (3, 5, 8, 11):
        cycle = [set(((i-1) % n, (i+1) % n)) for i in range(n)]
        assert one_target(cycle, 0) == Q((n-1)*(n-2), 6)
    barbell = [{1, 2}, {0, 2}, {0, 1, 3}, {2, 4, 5}, {3, 5}, {3, 4}]
    gaps = [one_target(barbell, t) for t in range(6)]
    print("Four cycle formulas checked exactly. Six barbell target gaps:", *gaps)


if __name__ == "__main__":
    main()
