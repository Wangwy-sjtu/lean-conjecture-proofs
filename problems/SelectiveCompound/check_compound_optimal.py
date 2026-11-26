"""Enumerate topologically labelled DAGs and compute the ordinary compound mex."""

from itertools import product


def compound_rows(moves, max_heap):
    """Use actual option pairs, processed in one topological order."""
    depths = []
    rows = []
    for position, successors in enumerate(moves):
        depth = max((depths[b] + 1 for b in successors), default=0)
        depths.append(depth)
        rows.append([])
        for heap in range(max_heap + 1):
            options = [(position, j) for j in range(heap)]
            options += [(b, j) for b in successors for j in range(heap + 1)]
            excluded = {rows[b][j] for b, j in options}
            value = 0
            while value in excluded:
                value += 1
            rows[position].append(value)
            assert heap <= value <= heap + depth
            assert value <= heap + len(successors) * (heap + 1)
            if heap:
                assert rows[position][heap - 1] < value
            if depth * depth // 4 <= heap:
                assert value == heap + depth
    return depths, rows


def main():
    graph_count = 0
    position_heaps = 0
    vertex_count = 6
    max_heap = 12
    worst_cutoff = [0] * vertex_count
    possible_moves = [
        [tuple(j for j in range(i) if mask & (1 << j)) for mask in range(1 << i)]
        for i in range(vertex_count)
    ]
    for moves in product(*possible_moves):
        depths, rows = compound_rows(moves, max_heap)
        for depth, row in zip(depths, rows):
            cutoff = next(k for k, val in enumerate(row) if val == k + depth)
            worst_cutoff[depth] = max(worst_cutoff[depth], cutoff)
        graph_count += 1
        position_heaps += len(moves) * (max_heap + 1)
    assert worst_cutoff == [d*d//4 for d in range(vertex_count)]

    path_moves = [()] + [(n - 1,) for n in range(1, 67)]
    depths, rows = compound_rows(path_moves, 64)
    for k in range(65):
        assert rows[k + 2][k] < k + depths[k + 2]

    stacks = 0
    stack_checks = 0
    for m in range(17):
        moves = [tuple(range(i)) for i in range(m + 1)]
        moves.extend((i - 1,) for i in range(m + 1, 2*m + 2))
        depths, rows = compound_rows(moves, m * (m + 1) + 3)
        for t in range(m+1):
            depth = m+t+1
            assert depths[depth] == depth
            for k, val in enumerate(rows[depth]):
                assert (val == k+depth) == (k >= m*(t+1))
                stack_checks += 1
            stacks += 1
    print(f"Graphs with six topologically labelled vertices: {graph_count:,}")
    print(f"Position/heap checks on these graphs: {position_heaps:,}")
    print(f"Worst cutoffs at depths 0 through 5: {worst_cutoff}")
    print("Explicit take-one witnesses checked for heap sizes 0 through 64.")
    print(f"Exact cutoff equivalences checked: {stack_checks:,} in {stacks} stack positions.")


if __name__ == "__main__":
    main()
