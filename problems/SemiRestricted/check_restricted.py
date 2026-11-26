"""Check the shuffle bound by exact event recursion and small minimax linear programs."""

from fractions import Fraction as F
from functools import cache
from itertools import combinations, product


def solve_square(matrix):
    """Solve a nonsingular augmented rational system by elimination."""
    rows = [[F(x) for x in row] for row in matrix]
    n = len(rows)
    for i in range(n):
        pivot = next((j for j in range(i, n) if rows[j][i]), None)
        if pivot is None:
            return None
        rows[i], rows[pivot] = rows[pivot], rows[i]
        rows[i] = [x / rows[i][i] for x in rows[i]]
        for j in range(n):
            if j != i and rows[j][i]:
                factor = rows[j][i]
                rows[j] = [x - factor * y for x, y in zip(rows[j], rows[i])]
    return [row[-1] for row in rows]


def matrix_value(rows):
    """Minimize the largest expected row over all probability vectors on columns."""
    cols = len(rows[0])
    best = None
    for t in range(1, min(len(rows), cols) + 1):
        for support in combinations(range(cols), t):
            for active in combinations(rows, t):
                eqs = [[1] * t + [0, 1]]
                eqs.extend([row[i] for i in support] + [-1, 0] for row in active)
                answer = solve_square(eqs)
                if answer is None:
                    continue
                p, val = answer[:-1], answer[-1]
                if min(p) < 0 or any(sum(q * row[i] for q, i in zip(p, support)) > val
                                      for row in rows):
                    continue
                best = val if best is None else min(best, val)
    assert best is not None
    return best


def check_graph(payoff, max_quota, use_minimax):
    k = len(payoff)

    @cache
    def values(r):
        n = sum(r)
        if not n:
            return F(0), F(0)
        legal = [i for i in range(k) if r[i]]
        future = [values(tuple(x - (j == i) for j, x in enumerate(r))) for i in legal]
        row_totals = [sum(row[i] * r[i] for i in legal) for row in payoff]
        baseline = max(row_totals)
        # With uniform play, the future state does not depend on the opponent's current row.
        uniform = (baseline + sum(r[i] * result[0] for i, result in zip(legal, future))) / n
        assert baseline <= uniform
        assert (uniform - baseline) ** 2 <= 225 * k ** 3 * max(r)
        if use_minimax:
            game = matrix_value([[row[i] + val for i, (_, val) in zip(legal, future)]
                                 for row in payoff])
            assert baseline <= game <= uniform
        else:
            game = None
        return uniform, game

    for quotas in product(range(max_quota + 1), repeat=k):
        values(quotas)
    return values.cache_info().currsize


def main():
    total = exact = 0
    for k, max_quota in [(1, 3), (2, 3), (3, 3), (4, 2)]:
        edges = list(combinations(range(k), 2))
        for signs in product((-1, 0, 1), repeat=len(edges)):
            payoff = [[0] * k for _ in range(k)]
            for (a, b), sign in zip(edges, signs):
                payoff[a][b], payoff[b][a] = sign, -sign
            count = check_graph(payoff, max_quota, k <= 3)
            total += count
            if k <= 3:
                exact += count
    print(f"Uniform-deck dynamic programs checked: {total} graph/quota pairs")
    print(f"Exact minimax values from rational linear programs: {exact} graph/quota pairs")


if __name__ == "__main__":
    main()
