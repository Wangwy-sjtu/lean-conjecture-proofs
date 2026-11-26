"""Enumerate topologically labelled DAGs and compute the ordinary compound mex."""

from itertools import product
from math import comb


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
            if comb(depth, 2) <= heap:
                assert value == heap + depth
    return depths, rows


def main():
    graph_count = 0
    position_heaps = 0
    vertex_count = 6
    max_heap = 12
    possible_moves = [
        [tuple(j for j in range(i) if mask & (1 << j)) for mask in range(1 << i)]
        for i in range(vertex_count)
    ]
    for moves in product(*possible_moves):
        compound_rows(moves, max_heap)
        graph_count += 1
        position_heaps += len(moves) * (max_heap + 1)

    path_moves = [()] + [(n - 1,) for n in range(1, 67)]
    depths, rows = compound_rows(path_moves, 64)
    for k in range(65):
        assert rows[k + 2][k] < k + depths[k + 2]

    print(f"Graphs with six topologically labelled vertices: {graph_count:,}")
    print(f"Position/heap checks on these graphs: {position_heaps:,}")
    print("Explicit take-one witnesses checked for heap sizes 0 through 64.")


if __name__ == "__main__":
    main()
