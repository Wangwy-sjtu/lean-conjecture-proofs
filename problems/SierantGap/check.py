"""Independent integer enumeration for the eight rank bounds at n=2."""
from itertools import combinations, product
from math import prod
from fractions import Fraction


def rows(x, u, v, y):
    return (x, x ^ u, x ^ v, x ^ u ^ v, y, y ^ u, y ^ v, y ^ u ^ v)


def main():
    code = [rows(*p) for p in product(range(2), repeat=4)]
    bases = [s for s in combinations(range(8), 4)
             if len({tuple(z[i] for i in s) for z in code}) == 16]
    d = 4
    strides = [d ** i for i in range(8)]
    counts = [0] * (d ** 8)
    for p in product(range(d), repeat=4):
        label = rows(*p)
        counts[sum(x * scale for x, scale in zip(label, strides))] += 1
    for scale in strides:
        for index in range(len(counts)):
            if (index // scale) % d:
                counts[index] += counts[index - scale]

    best = Fraction(0)
    witness = None
    for index, count in enumerate(counts):
        widths = tuple(1 + (index // scale) % d for scale in strides)
        min_basis = min(prod(widths[i] for i in s) for s in bases)
        assert min_basis <= 4 * count
        ratio = Fraction(min_basis, count)
        if ratio > best:
            best, witness = ratio, (widths, min_basis, count)
    print(f'n=2, {len(bases)} bases, {len(counts)} rank tuples; maximum basis/count = {best}')
    print(f'first maximizing tuple, minimum basis product, exact count = {witness}')
    flat5 = sum(all(x < 5 for x in rows(*p)) for p in product(range(8), repeat=4))
    print(f'n=3, eight widths equal to 5: {flat5} cubes, basis product {5**4}')
    assert flat5 == 313


if __name__ == '__main__':
    main()
