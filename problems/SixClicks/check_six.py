"""Independent bit-level audit of the nullity-six seed and worst-state witnesses."""
from collections import defaultdict
from check_scaling import basis, chase, columns, reflect


def all_seeds(vectors):
    result = [[0] * 11]
    for v in vectors:
        result += [[a ^ b for a, b in zip(mask, v)] for mask in result]
    return result


def seed_and_witness():
    vecs = basis(11)
    groups = defaultdict(list)
    for i, v in enumerate(columns(11, vecs)):
        groups[v].append(i)
    assert len(vecs) == 6 and len(groups[0]) == 9
    assert sum(len(c) for s, c in groups.items() if s) == 112
    assert all(len(c) % 2 == 0 for s, c in groups.items() if s)
    hard = [0] * 11
    for s, c in groups.items():
        for i in (c if s == 0 else c[:len(c) // 2]):
            hard[i // 11] |= 1 << (i % 11)
    masks = all_seeds(vecs)
    assert len({m[0] for m in masks}) == 64
    for b in masks:
        assert chase(11, b[0]) == (b, 0)
        assert sum((x ^ y).bit_count() for x, y in zip(hard, b)) == 65
    return masks, hard


def check():
    masks, hard = seed_and_witness()
    sizes = []
    for q in [*range(1, 22, 2), 27, 31, 37]:
        n = 12 * q - 1
        if len(basis(n)) != 6:
            continue
        witness = reflect(11, q, hard)
        separators = sum(1 << j for j in range(11, n, 12))
        for i, row in enumerate(witness):
            witness[i] = (1 << n) - 1 if i % 12 == 11 else row | separators
        for seed in masks:
            temp = reflect(11, q, seed)
            assert chase(n, temp[0]) == (temp, 0)
            assert sum((x ^ y).bit_count() for x, y in zip(witness, temp)) == 88*q*q - 24*q + 1
        sizes.append(n)
    print(f"All 64 physical seed solutions checked on {len(sizes)} equal-nullity "
          f"boards including all solutions to an explicit hardest state: {sizes}.")


if __name__ == "__main__":
    check()
