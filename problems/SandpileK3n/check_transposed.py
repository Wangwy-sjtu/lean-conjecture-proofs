"""Enumerate edge orientations of K(m,3), with the sink in the m-part."""

from collections import Counter
from itertools import accumulate, product
from math import comb


def orientation_counts(m):
    states = set()
    for rows in product(range(7), repeat=m - 1):
        # Bit j means the edge points from this nonsink left vertex to right vertex j.
        # Mask seven makes this left indegree zero and permits no stable lack.
        left = [range(3 - mask.bit_count()) for mask in rows]
        incoming = [sum((mask >> j) & 1 for mask in rows) for j in range(3)]
        for sink in range(8):
            right = [range(incoming[j] + ((sink >> j) & 1)) for j in range(3)]
            states.update(product(*(left + right)))
    counts = Counter(map(sum, states))
    return [counts[k] for k in range(max(counts) + 1)]


def formula_counts(m):
    n = m - 1
    trinomial = [1]
    for _ in range(n):
        old = [0, 0] + trinomial + [0, 0]
        trinomial = [sum(old[i : i + 3]) for i in range(len(old) - 2)]
    differences = []
    for k, a in enumerate(trinomial):
        j = k - n - 1
        differences.append(a - (3 * comb(n, j) * 2**j if j >= 0 else 0))
    return list(accumulate(accumulate(accumulate(differences))))


if __name__ == "__main__":
    for m in range(2, 7):
        direct = orientation_counts(m)
        assert direct == formula_counts(m), (m, direct, formula_counts(m))
        print(f"K({m},3) {direct}")
