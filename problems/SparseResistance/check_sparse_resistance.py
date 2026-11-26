"""Exact independent check on every labelled connected 2-sparse graph up to order six."""

from collections import Counter
from itertools import combinations


def tree_degrees(n, edges):
    """Enumerate spanning trees directly. Reject cycles while joining components."""
    for chosen in combinations(edges, n - 1):
        parent = list(range(n))
        degree = [0] * n

        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v

        for a, b in chosen:
            x, y = root(a), root(b)
            if x == y:
                break
            parent[x] = y
            degree[a] += 1
            degree[b] += 1
        else:
            yield tuple(degree)


def rn_witness(n, trees):
    """Test the uniform positive law, then seek an exact obstruction to every positive law."""
    if all(sum(row[v] for row in trees) <= 2 * len(trees) for v in range(n)):
        return True
    for size in range(1, n + 1):
        for subset in combinations(range(n), size):
            excess = [sum(row[v] - 2 for v in subset) for row in trees]
            if min(excess) >= 0 and max(excess) > 0:
                return False
    raise AssertionError("Neither an explicit positive law nor a dual witness was found")


def classify(n, edges, degrees):
    if max(degrees) <= 2:
        return "cycle" if all(d == 2 for d in degrees) else "path"
    if n == 5:
        hubs = {v for v, degree in enumerate(degrees) if degree == 3}
        complete_crossing = {(a, b) for a, b in combinations(range(n), 2)
                             if (a in hubs) != (b in hubs)}
        if len(hubs) == 2 and set(edges) == complete_crossing:
            return "K2,3"
    return "excluded"


def main():
    counts = Counter()
    for n in range(1, 7):
        possible = list(combinations(range(n), 2))
        # No RN assumption enters the enumeration; all graph masks are visited.
        for mask in range(1 << len(possible)):
            if mask.bit_count() < n - 1:
                continue
            edges = [e for i, e in enumerate(possible) if (mask >> i) & 1]
            degrees = [0] * n
            for a, b in edges:
                degrees[a] += 1
                degrees[b] += 1
            if any(degrees[a] > 2 and degrees[b] > 2 for a, b in edges):
                continue
            trees = list(tree_degrees(n, edges))
            if not trees:
                continue
            observed = rn_witness(n, trees)
            shape = classify(n, edges, degrees)
            assert observed == (shape != "excluded"), (n, edges, observed, shape)
            counts[shape] += 1
    for key in ("path", "cycle", "K2,3", "excluded"):
        print(f"{key}: {counts[key]}")
    print(f"Total connected labelled 2-sparse graphs checked: {sum(counts.values())}")


if __name__ == "__main__":
    main()
