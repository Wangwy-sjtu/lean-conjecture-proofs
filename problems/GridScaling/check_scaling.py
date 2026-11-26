"""Physical row-chasing checks and active-coordinate statistics."""
from collections import Counter
from itertools import product


def chase(n, first):
    mask = (1 << n) - 1
    prev, row = 0, first
    rows = []
    for _ in range(n):
        rows.append(row)
        prev, row = row, (row ^ prev ^ (row << 1) ^ (row >> 1)) & mask
    return rows, row


def basis(n):
    pivots, kernel = {}, []
    for j in range(n):
        first = 1 << j
        residue = chase(n, first)[1]
        while residue:
            lead = residue.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = residue, first
                break
            lower, vector = pivots[lead]
            residue ^= lower
            first ^= vector
        else:
            kernel.append(chase(n, first)[0])
    return kernel


def columns(n, basis_rows):
    return [sum(((rows[i] >> j) & 1) << k for k, rows in enumerate(basis_rows))
            for i, j in product(range(n), repeat=2)]


def reflect(n, q, rows):
    def index(i):
        tile, coord = divmod(i, n + 1)
        if coord == n:
            return None
        return coord if tile % 2 == 0 else n - 1 - coord

    coords = [index(i) for i in range((n + 1) * q - 1)]
    return [sum(((rows[r] >> c) & 1) << j for j, c in enumerate(coords)
                if r is not None and c is not None) for r in coords]


def check():
    equal = grids = 0
    for m, q in product(range(1, 18), range(1, 7)):
        n = (m + 1) * q - 1
        seed, large = basis(m), basis(n)
        seed_columns = columns(m, seed)
        active = sum(x != 0 for x in seed_columns)
        lifted = [reflect(m, q, b) for b in seed]
        for rows in lifted:
            generated, residue = chase(n, rows[0])
            assert residue == 0 and generated == rows
        physical = Counter(columns(n, lifted))
        assert all(physical[k] == q*q*v for k, v in Counter(seed_columns).items() if k)
        assert physical[0] == n*n - q*q*active
        assert len(seed) <= len(large)
        if len(seed) == len(large):
            equal += 1
        grids += 1
    print(f"Verified reflected physical bases, cell multiplicities and all zero "
          f"coordinates on {grids} boards, including {equal} equal-nullity dilations.")
    for m in (4, 5, 9, 11, 16, 29):
        seed = basis(m)
        c = Counter(columns(m, seed))
        odd = sorted(k for k,v in c.items() if k and v%2)
        print(m,len(seed),sum(v for k,v in c.items() if k),len(odd),Counter(c.values()))
        if len(odd) <= 40:
            print("odd types",odd)


if __name__ == "__main__":
    check()
