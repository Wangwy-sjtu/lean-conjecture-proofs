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



def check_counterexample():
    color = (2, 0, 0, 0, 1, 1, 1)
    edges = {(u, v) for u, v in combinations(range(7), 2) if color[u] != color[v]}
    program = ((4,3), (2,6), (1,5), (1,4), (0,2), (0,1), (1,4),
               (4,3), (2,4), (1,5), (2,6), (6,1), (5,2), (3,5),
               (6,3), (0,6), (6,1), (6,3), (3,5), (5,2), (2,4))
    state = [1 << i for i in range(7)]
    seen = []
    for control, target in program:
        state[target] ^= state[control]
        seen.append(state[target])
    required = {(1 << u) | (1 << v) for u, v in edges}
    assert len(program) == len(edges) + 7 - 1
    assert set(seen[:15]) == required and state == [1 << i for i in range(7)]

    # Deleting any one vertex leaves a connected graph.
    for missing in range(7):
        reached = {next(i for i in range(7) if i != missing)}
        for _ in range(6):
            reached.update(i for i in range(7) if i != missing
                           and any(color[j] != color[i] for j in tuple(reached)))
        assert len(reached) == 6

    def valid_order(order):
        for k, pivot in enumerate(order):
            later = [j for j in order[k+1:] if color[j] != color[pivot]]
            if any(color[x] == color[y] for x, y in zip(later, later[1:])):
                return False
        return True

    assert sum(valid_order(order) for order in permutations(range(7))) == 0
    print("K(1,3,3): 15 edges visited in 21 gates, identity restored, 0 of 5040 orders valid.")


if __name__ == "__main__":
    check_counterexample()
    check_four_wires()
    for leaves in range(2, 31):
        check_two_hubs(leaves)
    print("K(2,p): the 3p+2-gate construction covers every edge and restores every wire for 2 ≤ p ≤ 30.")
