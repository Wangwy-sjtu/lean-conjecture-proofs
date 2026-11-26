"""Independent checks for the nullity-four Most Clicks formula. Uses Python's standard library."""
from collections import Counter


def chase(side, top):
    above, row = 0, top
    mask = (1 << side) - 1
    rows = []
    for _ in range(side):
        rows.append(row)
        above, row = row, (above ^ row ^ (row << 1) ^ (row >> 1)) & mask
    return rows, row


def nullity(side):
    pivots = {}
    for j in range(side):
        value = chase(side, 1 << j)[1]
        while value:
            lead = value.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = value
                break
            value ^= pivots[lead]
    return side - len(pivots)


def pack(rows):
    return sum(row << (4 * i) for i, row in enumerate(rows))


def tile_coordinate(index):
    block, slot = divmod(index, 5)
    if slot == 4:
        return None
    return block, (slot if block % 2 == 0 else 3 - slot)


def tile_board(side, fill, gap):
    coordinates = [tile_coordinate(i) for i in range(side)]
    rows = []
    for row in coordinates:
        bits = 0
        for j, col in enumerate(coordinates):
            if row is None or col is None:
                bit = gap
            else:
                block_row, i = row
                block_col, k = col
                bit = (fill(block_row, block_col) >> (4*i + k)) & 1
            bits |= bit << j
        rows.append(bits)
    return rows


def check():
    masks = []
    for top in range(16):
        rows, boundary = chase(4, top)
        assert boundary == 0
        masks.append(pack(rows))
    assert len(set(masks)) == 16
    radii = [min((word ^ p).bit_count() for p in masks) for word in range(1 << 16)]
    assert max(radii) == radii[0x1bd] == 7
    for fixed in (0, 1):
        group = [p for p in masks if ((p >> 1) & 1) == fixed]
        counts = [sum((p >> j) & 1 for p in group) for j in range(16)]
        assert counts[1] == 8*fixed
        assert Counter(counts[j] for j in range(16) if j != 1) == {4: 15}

    sizes = []
    for q in range(1, 32, 2):
        side = 5*q - 1
        if nullity(side) != 4:
            continue
        costs = []

        def fill(i, j):
            place = i*q+j
            if place == 0:
                return 0x1bd
            return 0xffff if place % 2 else 0

        witness = tile_board(side, fill, 1)
        for mask in masks:
            rows = tile_board(side, lambda _i, _j: mask, 0)
            actual, last = chase(side, rows[0])
            assert last == 0 and rows == actual
            costs.append(sum((a ^ b).bit_count() for a, b in zip(rows, witness)))
        assert min(costs) == 17*q*q-10*q
        sizes.append(side)
    print(f"Exhausted 65,536 seed words. Checked all 16 solutions of the constructed "
          f"worst-case instance on each of {len(sizes)} larger-or-equal boards: {sizes}.")


if __name__ == "__main__":
    check()
