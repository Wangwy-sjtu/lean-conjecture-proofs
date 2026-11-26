# A seven-vertex counterexample to the characterization of perfect graphic parity networks

The complete tripartite graph $K_{1,3,3}$ admits a perfect graphic parity network and has no perfect cancellation ordering. This answers the main question in §4 of *Toward Minimum Graphic Parity Networks* in the negative. Cao, Lu, Nie, Sun and Tian proved the forward construction from an ordering to a circuit. The counterexample refutes the converse, stated as Conjecture 18 in the authors’ manuscript. [Original arXiv paper, §§2.2 and 4](https://arxiv.org/html/2509.10070v1#S4) · [Conjecture 18, page 13](https://yiren.lu/assets/pdf/parity-network.pdf#page=13)

## A circuit attaining the lower bound

Let 0 be the apex and let the two independent parts be $A=\{1,2,3\}$ and $B=\{4,5,6\}$. The graph has seven vertices and fifteen edges. In the model of the paper, wires start at the seven independent inputs, a CNOT adds its control to its target over $\mathbb F_2$, and every wire must finish at its own input. For a connected graph with $m$ edges and $n$ vertices, a perfect circuit uses $m+n-1$ gates. Here that number is 21. [Original circuit definition and lower bound](https://arxiv.org/html/2509.10070v1#S2)

Each row of the table gives the target’s support immediately after the gate. The first fifteen gates produce each of the fifteen edge parities exactly once. The last six restore wires 6, 1, 3, 5, 2 and 4 in that order. Wire 0 retains its original value throughout.

| Gate | Control → target | Output support |
| ---: | :---: | :--- |
| 1 | 4 → 3 | {3,4} |
| 2 | 2 → 6 | {2,6} |
| 3 | 1 → 5 | {1,5} |
| 4 | 1 → 4 | {1,4} |
| 5 | 0 → 2 | {0,2} |
| 6 | 0 → 1 | {0,1} |
| 7 | 1 → 4 | {0,4} |
| 8 | 4 → 3 | {0,3} |
| 9 | 2 → 4 | {2,4} |
| 10 | 1 → 5 | {0,5} |
| 11 | 2 → 6 | {0,6} |
| 12 | 6 → 1 | {1,6} |
| 13 | 5 → 2 | {2,5} |
| 14 | 3 → 5 | {3,5} |
| 15 | 6 → 3 | {3,6} |
| 16 | 0 → 6 | {6} |
| 17 | 6 → 1 | {1} |
| 18 | 6 → 3 | {3} |
| 19 | 3 → 5 | {5} |
| 20 | 5 → 2 | {2} |
| 21 | 2 → 4 | {4} |

The circuit was found by starting with the edge parities of a spanning tree. If two wires carry two edges of a triangle, a CNOT can replace one with the third edge. Keeping the child of the initial rooted tree on its wire made the resulting final tree easy to uncompute.

## Why every ordering fails

In a perfect cancellation ordering, for a vertex $v$ and each connected component of $G-v$, the neighbors of $v$ that occur later in the order and belong to the component must form a path in that same order. Here $G-v$ is connected for every $v$.

Take the first vertex $v$ from $A\cup B$ in any proposed ordering. All three vertices of the opposite part are later neighbors of $v$. They are pairwise nonadjacent. The only other possible later neighbor is the apex 0. Three pairwise nonadjacent vertices need at least two separators to appear consecutively along a path. The one available apex cannot provide them. This contradiction rules out every ordering. [Definition in §2.2](https://arxiv.org/html/2509.10070v1#S2.SS2)

## Verification

The Lean theorem `CaoCounterexample.counterexample` combines connectedness, the length and coverage of the concrete circuit, exact restoration and the absence of an ordering. `edge_iff` identifies the edge-support and vertex-color presentations on the same seven vertices. `Multipartite.graphOrdering` uses reachability after deletion of the pivot, and `Multipartite.named_vertices` handles arbitrary permutations of the named vertices. `by decide` reduces the finite gate certificate in the kernel. The proofs report only `propext`, `Classical.choice` and `Quot.sound`. An independent Python program also enumerates all $7!=5040$ vertex orders. [Lean certificate](CaoCounterexample.lean) · [Independent checker](check_small.py)

The public-source check considered the paper and authors’ later manuscript, citing records, variations of the graph’s name, GitHub code and issues, and indexed AI proof archives. The two works returned by OpenAlex as citing this preprint concern implementing a prescribed binary matrix and selecting phase-term orders. A public AI proof for another diagonal-unitary problem contains the birth-span and conservation count used in the **separate triangle-free result** in this package. The seven-vertex counterexample above is self-contained. No earlier public instance of this counterexample was located in the searches of 27 November 2026. [Matrix-distance paper](https://arxiv.org/abs/2608.03825) · [Phase-order paper](https://arxiv.org/abs/2608.27592) · [Prior AI counting argument, step 4](https://github.com/the-omega-institute/trureturing/issues/24527)
