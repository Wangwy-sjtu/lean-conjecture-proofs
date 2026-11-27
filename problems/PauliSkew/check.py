"""Exact integer cross-check of the two-qubit skew certificate. Python 3.10+."""
from collections import Counter, deque
from itertools import combinations, permutations, product
from pathlib import Path
import re

ZERO, ONE, IM = (0, 0), (1, 0), (0, 1)


def scale(k, z):
    return k*z[0], k*z[1]


def mul(z, w):
    return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]


def total(terms):
    real, imag = 0, 0
    for a, b in terms:
        real += a
        imag += b
    return real, imag


def matrix(f, n=4):
    return tuple(tuple(f(i, j) for j in range(n)) for i in range(n))


def mm(a, b):
    return matrix(lambda i, j: total(mul(a[i][k], b[k][j]) for k in range(4)))


def adj(a):
    return matrix(lambda i, j: (a[j][i][0], -a[j][i][1]))


def kron(a, b):
    return matrix(lambda i, j: mul(a[i//2][j//2], b[i%2][j%2]))


I = ((ONE, ZERO), (ZERO, ONE))
X = ((ZERO, ONE), (ONE, ZERO))
Y = ((ZERO, (0, -1)), (IM, ZERO))
Z = ((ONE, ZERO), (ZERO, (-1, 0)))
PAULI = [kron(p, q) for p, q in product((I, X, Y, Z), repeat=2)][1:]
LOOKUP = {matrix(lambda i, j: scale(t, p[i][j])): (k, t)
          for k, p in enumerate(PAULI) for t in (-1, 1)}


def geometry():
    points = range(15)
    commuting = []
    for i, j in product(points, repeat=2):
        prod = mm(PAULI[i], PAULI[j])
        if i != j and prod == mm(PAULI[j], PAULI[i]):
            third, sign = LOOKUP[prod]
            assert third+1 == ((i+1) ^ (j+1))
            commuting.append((i, j, third, sign))
    assert len(commuting) == 90
    lines = sorted({tuple(sorted(triple[:3])) for triple in commuting})
    tests = [order for line in lines for order in permutations(line)]
    signmap = {(i,j,k): t for i,j,k,t in commuting}
    signs = [signmap[t] for t in tests]
    for i in range(15):
        assert len(set(signs[6*i:6*i+6])) == 1

    rulings = {}
    for subset in combinations(range(15), 3):
        union = frozenset(x for i in subset for x in lines[i])
        if len(union) == 9:
            rulings.setdefault(union, []).append(subset)
    grids = [pair for pair in rulings.values() if len(pair) == 2]
    assert len(grids) == 10
    contexts = []
    for rows, cols in grids:
        grid = [[next(iter(set(lines[i]) & set(lines[j]))) for j in cols] for i in rows]
        for color in permutations(range(3)):
            tests_in_context = []
            for transpose in (False, True):
                for k in range(3):
                    ordered = [None]*3
                    for h in range(3):
                        i, j = (h, k) if transpose else (k, h)
                        ordered[color[(i+j) % 3]] = grid[i][j]
                    tests_in_context.append(tests.index(tuple(ordered)))
            assert sum(signs[e] < 0 for e in tests_in_context) % 2 == 1
            for role in range(3):
                counts = Counter(tests[e][role] for e in tests_in_context)
                assert all(n % 2 == 0 for n in counts.values())
            contexts.append(tests_in_context)
    assert Counter(e for context in contexts for e in context) == Counter({e: 4 for e in range(90)})
    assert sum(x < 0 for x in signs) % 2 == 0
    for role in range(3):
        assert Counter(t[role] for t in tests) == Counter({i: 6 for i in points})
    print('15 Pauli lines, 90 ordered products, 10 grids, 60 odd contexts, coverage exactly 4.')
    return commuting, tests, signs, contexts


def verify_packed(tests, signs, contexts):
    source = Path(__file__).with_name('PauliSkew.lean').read_text()
    inverse = {(t[0],t[1]): i for i,t in enumerate(tests)}
    tables = [('point', 4, [v for t in tests for v in t]),
              ('negative', 1, [int(s < 0) for s in signs]),
              ('inversePair', 7, [inverse.get((i,j), 0) for i,j in product(range(15), repeat=2)]),
              ('context', 7, [e for c in contexts for e in c])]
    for name, bits, entries in tables:
        m = re.search(r'^.*def '+name+r' \(.*?\n.*?(0x[0-9a-f]+)', source, re.M)
        assert m and int(m[1], 16) == sum(v << (bits*i) for i,v in enumerate(entries))
    print('All four packed tables in the Lean source exactly match direct matrix reconstruction.')


def clifford_actions():
    h = ((ONE, ONE), (ONE, (-1, 0)))
    s = ((ONE, ZERO), (ZERO, IM))
    cnot = matrix(lambda i, j: (int(i == (j ^ ((j >> 1) & 1))), 0))
    actions = []
    gates = [(kron(h, I), 2), (kron(I, h), 2), (kron(s, I), 1), (kron(I, s), 1), (cnot, 1)]
    for gate, denominator in gates:
        permutation = []
        for p in PAULI:
            image = mm(mm(adj(gate), p), gate)
            assert all(k % denominator == 0 for row in image for z in row for k in z)
            exact = matrix(lambda i,j: tuple(k//denominator for k in image[i][j]))
            permutation.append(LOOKUP[exact])
        assert len({i for i, t in permutation}) == 15
        flips = sum((t < 0) << i for i,t in permutation)
        chunks = [[sum(((z >> i) & 1) << permutation[i+off][0] for i in range(5))
                   for z in range(32)] for off in (0, 5, 10)]
        actions.append((flips, chunks))
    return actions


def sharpen(commuting):
    # Clifford conjugation signed-permutes all three functions together. For a
    # fixed first orbit representative, enumerate the second sign function; the
    # maximizing third function takes the sign of each resulting coefficient.
    actions = clifford_actions()
    unseen = set(range(1 << 15))
    orbit_data = []
    while unseen:
        first = min(unseen)
        unseen.remove(first)
        size, queue = 1, deque([first])
        while queue:
            mask = queue.popleft()
            for flip, (low, middle, high) in actions:
                image = flip ^ low[mask & 31] ^ middle[(mask >> 5) & 31] ^ high[mask >> 10]
                if image in unseen:
                    unseen.remove(image)
                    queue.append(image)
                    size += 1
        terms = [[(i, j, sign) for i,j,k,sign in commuting if k == col] for col in range(15)]
        masks = [sum(1 << j for _, j, _ in v) for v in terms]
        flips = [sum(1 << j for i,j,sign in v if bool((first >> i) & 1) != (sign < 0))
                 for v in terms]
        assert all(m.bit_count() == 6 for m in masks)
        best = max(sum(abs(6-2*((second & m)^f).bit_count()) for m,f in zip(masks,flips))
                   for second in range(1 << 15))
        orbit_data.append((first, size, best))
    assert len(orbit_data) == 12 and sum(size for _,size,_ in orbit_data) == 32768
    assert max(value for _,_,value in orbit_data) == 54
    assert sum(sign for _,_,_,sign in commuting) == 54
    print('Independent exhaustive trilinear norm: 54, attained by three constant +1 functions.')
    print('First-sign Clifford orbit frequencies by largest mixed trilinear value:',
          sorted(Counter(value for _,_,value in orbit_data).items()))


if __name__ == '__main__':
    commuting, tests, signs, contexts = geometry()
    verify_packed(tests, signs, contexts)
    sharpen(commuting)
