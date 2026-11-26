"""Cross-check the coefficient formula by enumerating every labelled edge orientation."""

from collections import Counter
from itertools import accumulate, product
from math import comb


def orientation_counts(n):
    states = set()
    for columns in product(range(1, 8), repeat=n):
        # The excluded all-zero column has right indegree zero.
        first = sum(mask & 1 for mask in columns)
        second = sum((mask >> 1) & 1 for mask in columns)
        if max(first, second) >= n:
            continue
        bounds = [range(n - first), range(n - second)]
        bounds += [range(mask.bit_count()) for mask in columns]
        states.update(product(*bounds))
    degrees = Counter(map(sum, states))
    return [degrees[k] for k in range(max(degrees) + 1)]


def formula_counts(n):
    trinomial = [1]
    for _ in range(n):
        old = [0, 0] + trinomial + [0, 0]
        trinomial = [sum(old[i : i + 3]) for i in range(len(old) - 2)]
    differences = [
        trinomial[k] - (2 * comb(n, k - n) * 2 ** (k - n) if k >= n else 0)
        for k in range(2 * n - 1)
    ]
    return list(accumulate(accumulate(differences)))


if __name__ == "__main__":
    for n in range(2, 7):
        direct = orientation_counts(n)
        assert direct == formula_counts(n), (n, direct, formula_counts(n))
        print(f"K(3,{n}) {direct}")
