"""Check the counterexample, enumerate four-wire networks, and simulate pair circuits."""
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



def check_complete_bipartite(a, b):
    """Simulate the hub transitions and independently minimize the pivot bound."""
    hubs = range(a)
    leaves = range(a, a + b)
    gates = [(0, x) for x in leaves]
    for h in range(1, a):
        gates.append((h - 1, h))
        gates.extend((h, x) for x in leaves)
        gates.append((h - 1, h))
    gates.extend((a - 1, x) for x in leaves)

    start = [1 << x for x in range(a + b)]
    state = start.copy()
    seen = set()
    for control, target in gates:
        state[target] ^= state[control]
        seen.add(state[target])
    edges = {start[h] | start[x] for h in hubs for x in leaves}
    assert edges <= seen and state == start
    optimum = a * b + b + 2 * a - 2
    assert len(gates) == optimum
    lower = min(a * b + x + y + max(a + b - 1, (a - x) * (b - y))
                for x in range(a + 1) for y in range(b + 1))
    assert lower == optimum


def minimum_with_ancillas(a, b, clean, borrowed):
    """Meet-in-the-middle search on concrete forms including every auxiliary wire."""
    data = a + b
    start = tuple([1 << i for i in range(data + borrowed)] + [0] * clean)
    moves = list(permutations(range(len(start)), 2))
    terms = [(1 << i) | (1 << j) for i in range(a) for j in range(a, data)]
    flag = {term: 1 << i for i, term in enumerate(terms)}
    all_terms = (1 << len(terms)) - 1
    upper = a * b + b + 2 * a - 2
    # A path from the initial state followed by a reversed path from the
    # same endpoint visits exactly the union of the two sets of edge terms.
    depths = {(start, 0): 0}
    frontier = [(start, 0)]
    for k in range(1, (upper + 1) // 2 + 1):
        next_layer = []
        for state, seen in frontier:
            for c, t in moves:
                new = list(state)
                new[t] ^= new[c]
                key = (tuple(new), seen | flag.get(new[t], 0))
                if key not in depths:
                    depths[key] = k
                    next_layer.append(key)
        frontier = next_layer
    endpoints = defaultdict(list)
    for (state, seen), k in depths.items():
        endpoints[state].append((seen, k))
    return min(k + j for entries in endpoints.values()
               for mask, k in entries for other, j in entries if mask | other == all_terms)


def check_girth_bound():
    """Compare XOR collisions with four-cycles, then audit a running circuit."""
    tested = 0
    for n in range(1, 7):
        pairs = list(combinations(range(n), 2))
        for subset in range(1 << len(pairs)):
            adjacency = [set() for _ in range(n)]
            terms = set()
            for i, (v, w) in enumerate(pairs):
                if subset & (1 << i):
                    adjacency[v].add(w)
                    adjacency[w].add(v)
                    terms.add((1 << v) | (1 << w))
            differences = [e ^ f for e, f in combinations(terms, 2)]
            squares_absent = all(len(adjacency[v] & adjacency[w]) <= 1 for v, w in pairs)
            triangles_absent = all(not (adjacency[v] & adjacency[w])
                                   for v, w in pairs if w in adjacency[v])
            assert squares_absent == (len(differences) == len(set(differences)))
            assert triangles_absent == terms.isdisjoint(differences)
            tested += 1

    # Petersen graph, using an exceptional control to move directly between
    # two newly visited edges. The remaining edges are computed then uncomputed.
    edges = {tuple(sorted((i, (i + 1) % 5))) for i in range(5)}
    edges |= {tuple(sorted((i + 5, (i + 2) % 5 + 5))) for i in range(5)}
    edges |= {(i, i + 5) for i in range(5)}
    required = {(1 << u) | (1 << v) for u, v in edges}
    gates = [(1, 4), (1, 0), (4, 0), (1, 4), (4, 0)]
    for u, v in sorted(edges - {(0, 1), (0, 4)}):
        gates.extend(((u, v), (u, v)))
    start = [1 << v for v in range(10)]
    state = start.copy()
    seen, hot, charged, exceptions = set(), set(), set(), set()
    for k, (c, t) in enumerate(gates, 1):
        control = state[c]
        state[t] ^= control
        term = state[t]
        if term in required and term not in seen:
            if t in hot:
                assert control in exceptions and control not in charged
                charged.add(control)
            hot.add(t)
            seen.add(term)
        else:
            hot.discard(t)
        if term.bit_count() % 2 == 0 and term not in required:
            exceptions.add(term)
        assert 2 * len(seen) <= k + len(charged) + len(hot)
    assert state == start and seen == required and not hot and len(charged) == 1
    assert 3 * len(edges) + len(start) - 1 == 54
    print(f"{tested} labeled graphs: XOR uniqueness agrees with four-cycle exclusion; "
          "the Petersen circuit satisfies the counting invariant at every gate.")


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


def forest_half(vertices, edges):
    """Orient a forest, then build a path from identity to the full apex star."""
    neighbors = [[] for _ in range(vertices)]
    for u, v in edges:
        neighbors[u].append(v)
        neighbors[v].append(u)
    roots, oriented, visited = [], [], set()
    for root in range(vertices):
        if root in visited:
            continue
        roots.append(root)
        queue = [root]
        visited.add(root)
        for u in queue:
            for v in neighbors[u]:
                if v not in visited:
                    visited.add(v)
                    queue.append(v)
                    oriented.append((u, v))
    if len(oriented) != len(edges):
        return None
    return list(reversed(oriented)) + [(vertices, v) for v in roots] + oriented


def check_cone_program(vertices, first, second):
    assert set(first).isdisjoint(second)
    outward = forest_half(vertices, first)
    inward = forest_half(vertices, second)
    assert outward is not None and inward is not None
    gates = outward + list(reversed(inward))
    start = [1 << x for x in range(vertices + 1)]
    state = start.copy()
    required = {start[u] | start[v] for u, v in first + second}
    required.update(start[-1] | start[u] for u in range(vertices))
    seen = set()
    for c, t in gates:
        state[t] ^= state[c]
        assert state[t] & start[t] and state[t].bit_count() in (1, 2)
        seen.add(state[t])
    assert state == start and required <= seen and len(gates) == len(required) + vertices
    return len(gates)


def check_cone_forests():
    count = 0
    for n in range(7):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [edge for i, edge in enumerate(pairs) if mask & (1 << i)]
            if any((a, b) in edges and (a, c) in edges and (b, c) in edges
                   for a, b, c in combinations(range(n), 3)):
                continue
            for partition in range(1 << len(edges)):
                left = [e for i, e in enumerate(edges) if partition & (1 << i)]
                right = [e for i, e in enumerate(edges) if not partition & (1 << i)]
                if forest_half(n, left) is not None and forest_half(n, right) is not None:
                    check_cone_program(n, left, right)
                    count += 1
                    break
            else:
                raise AssertionError(("unexpected obstruction on six or fewer vertices", n, edges))
    # All 12 edges of K(3,4) split into the following two Hamiltonian paths.
    def path(vertices):
        return [tuple(sorted(e)) for e in zip(vertices, vertices[1:])]
    first = path([3, 0, 4, 1, 5, 2, 6])
    second = path([5, 0, 6, 1, 3, 2, 4])
    assert set(first + second) == {(a, b) for a in range(3) for b in range(3, 7)}
    assert check_cone_program(7, first, second) == 26
    print(f"{count} labeled triangle-free bases on at most six vertices: every constructed cone "
          "circuit covers its edges, attains the lower bound and satisfies C1 and C3 at every gate. "
          "The explicit K(1,3,4) circuit uses 26 gates.")


if __name__ == "__main__":
    check_counterexample()
    check_four_wires()
    for leaves in range(2, 31):
        check_two_hubs(leaves)
    print("K(2,p): the 3p+2-gate construction covers every edge and restores every wire for 2 ≤ p ≤ 30.")
    for a in range(1, 13):
        for b in range(a, 25):
            check_complete_bipartite(a, b)
    print("K(a,b): circuits and minima of the pivot bound agree for 1 ≤ a ≤ 12 and a ≤ b ≤ 24.")
    assert minimum_with_ancillas(1, 2, clean=1, borrowed=1) == 4
    assert minimum_with_ancillas(2, 2, clean=1, borrowed=0) == 8
    assert minimum_with_ancillas(2, 2, clean=0, borrowed=1) == 8
    print("With auxiliary wires: exact search gives 4 for a two-edge star with both kinds, "
          "and 8 for a four-cycle with a clean or borrowed wire.")
    check_girth_bound()
    check_cone_forests()
