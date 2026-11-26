"""Enumerate closed CNOT programs of length at most eight on four wires."""
from collections import defaultdict
from itertools import combinations, permutations


def check_four_wires():
    n = 4
    initial = tuple(1 << i for i in range(n))
    pairs = list(combinations(range(n), 2))
    bit = {initial[i] | initial[j]: 1 << k for k, (i, j) in enumerate(pairs)}
    moves = list(permutations(range(n), 2))
    depth = {(initial, 0): 0}
    frontier = [(initial, 0)]
    for length in range(1, 5):
        following = []
        for state, seen in frontier:
            for control, target in moves:
                new = list(state)
                new[target] ^= new[control]
                key = (tuple(new), seen | bit.get(new[target], 0))
                if key not in depth:
                    depth[key] = length
                    following.append(key)
        frontier = following
    by_state = defaultdict(list)
    for (state, seen), length in depth.items():
        by_state[state].append((seen, length))
    best = {}
    # Each gate is an involution. Two paths ending in the same state give a
    # closed walk; splitting at the middle recovers every walk of length ≤ 8.
    for ends in by_state.values():
        for first, a in ends:
            for second, b in ends:
                seen = first | second
                best[seen] = min(best.get(seen, 9), a + b)

    def minimum(edges):
        required = sum(bit[initial[i] | initial[j]] for i, j in edges)
        return min((value for mask, value in best.items() if mask & required == required),
                   default=None)

    count = {3: 0, 4: 0}
    for size in count:
        for edges in combinations(pairs, size):
            edge_set = set(edges)
            if any(set(combinations(triple, 2)) <= edge_set
                   for triple in combinations(range(n), 3)):
                continue
            reached = {0}
            for _ in range(n):
                for i, j in edges:
                    if i in reached or j in reached:
                        reached.update((i, j))
            if len(reached) == n:
                assert minimum(edges) == 2 * size, edges
                count[size] += 1
    assert count == {3: 16, 4: 3}
    print("4 wires: 16 labeled trees need 6 gates, 3 labeled four-cycles need 8.")


def check_two_hubs(p):
    state = [1 << i for i in range(p + 2)]
    start = state.copy()
    leaves = range(2, p + 2)
    gates = [(0, 1)]
    for x in leaves:
        gates.extend(((0, x), (1, x)))
    gates.append((0, 1))
    gates.extend((1, x) for x in reversed(leaves))
    seen = set()
    for control, target in gates:
        state[target] ^= state[control]
        seen.add(state[target])
    required = {start[h] | start[x] for x in leaves for h in (0, 1)}
    assert required <= seen and state == start and len(gates) == 3 * p + 2


if __name__ == "__main__":
    check_four_wires()
    for leaves in range(2, 31):
        check_two_hubs(leaves)
    print("K(2,p): the 3p+2-gate construction covers every edge and restores every wire for 2 ≤ p ≤ 30.")
