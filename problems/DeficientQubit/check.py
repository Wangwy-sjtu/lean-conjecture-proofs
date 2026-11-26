"""Exact rational cross-check of zero completions in all three deficient support types."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from collections import Counter


def matmul(left, right):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*right)] for row in left]


def transpose(matrix):
    return list(map(list, zip(*matrix)))


def determinant(a):
    if len(a) == 1:
        return a[0][0]
    return sum((-1)**j * x * determinant([r[:j]+r[j+1:] for r in a[1:]])
               for j, x in enumerate(a[0]))


def sign(x):
    return int(x > 0) - int(x < 0)


def check_completion(matrix, signs, strict):
    assert all(abs(z) <= 1 and z*x == abs(x)
               for row, mask in zip(matrix, signs) for x, z in zip(row, mask))
    so = matmul(signs, transpose(matrix))
    total = sum(so[i][i] for i in range(3))
    negative = [[(total if i == j else 0) - so[i][j] - so[j][i]
                 for j in range(3)] for i in range(3)]
    for k in (1, 2, 3):
        for indices in combinations(range(3), k):
            minor = determinant([[negative[i][j] for j in indices] for i in indices])
            assert minor > 0 if strict else minor >= 0


def main():
    angles = [(F(1), F(0)), (F(0), F(1)), (F(3, 5), F(4, 5)),
              (F(5, 13), F(12, 13)), (F(-7, 25), F(24, 25))]
    counts = Counter()
    for ((p, q), (r, s)), t, rows, cols in product(
            product(angles, repeat=2), (-1, 1), permutations(range(3)), permutations(range(3))):
        raw = [[t*q*s, -t*q*r, p], [-t*p*s, t*p*r, q], [r, s, F(0)]]
        matrix = [[raw[i][j] for j in cols] for i in rows]
        identity = matmul(matrix, transpose(matrix))
        assert identity == [[int(i == j) for j in range(3)] for i in range(3)]
        ep, eq, er, es = [(-1 if x < 0 else 1) for x in (p, q, r, s)]
        d = -t*ep*eq*er*es
        left, right = (ep, eq, d), (d*er, d*es, 1)
        base = ((-1, 1, 1), (1, -1, 1), (1, 1, 0))
        signs = [[left[i]*right[j]*base[i][j] for j in cols] for i in rows]
        check_completion(matrix, signs, strict=False)
        check_completion(matrix, [[sign(x) for x in row] for row in matrix], strict=True)
        counts[sum(x == 0 for row in matrix for x in row)] += 1
    assert set(counts) == {1, 4, 6}
    print('Exact rational completion and zero-fill checks, counted by zero entries')
    print(', '.join(f'{k} zeros: {v} matrices' for k, v in sorted(counts.items())))


if __name__ == '__main__':
    main()
