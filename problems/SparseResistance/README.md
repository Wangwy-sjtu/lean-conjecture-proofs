# 每条边至少有一个低度端点时，哪些图允许非负电阻曲率？

设 $G$ 是有限、简单、连通图。称 $G$ 为 **2-sparse 图**，如果每条边至少有一个端点的度数不超过 2。称 $G$ 为 **RN 图**，如果可以给每条边赋正电导，使每个顶点的 Devriendt–Lambiotte 电阻曲率都非负。**连通的 2-sparse RN 图恰为路径、环和完全二部图 $K_{2,3}$**。单顶点图作为路径计入。[2-sparse 的标准定义](https://www.sciencedirect.com/science/article/abs/pii/S0012365X23001206) · [电阻曲率的原论文](https://link.springer.com/article/10.1007/s00026-025-00774-x)

Devriendt 在 Question 6.9 中询问哪些双连通平面图是 RN。上面的分类给出该问题在 2-sparse 图上的全部答案，证明也适用于这一类里的非平面图。Garcia 的 Question 6.1 询问两侧大小相差一的连通二部 RN 图有何结构。在 2-sparse 条件下，两侧大小相差一的答案恰为奇数阶路径和 $K_{2,3}$。两篇论文的一般分类仍超出本文所得结果。[Devriendt，Question 6.9](https://link.springer.com/article/10.1007/s00026-025-00774-x) · [Garcia，Question 6.1](https://arxiv.org/html/2609.23394v1#S6)

## 从生成树和省略边计数

Devriendt 定理 3.8 证明，$G$ 是 RN 当且仅当其全部生成树上存在一个满支撑的概率分布，使每个顶点在随机树中的期望度不超过 2。“满支撑”指每一棵生成树的概率都严格大于零。令 $n=|V|$、$m=|E|$、$\beta=m-n+1$，并令 $q_e$ 等于边 $e$ 在随机生成树中被省略的概率。每棵树恰省略 $\beta$ 条边，而省略非桥后图仍连通。因此

$$
\sum_{e\in E}q_e=\beta,\qquad
q_e>0\quad(e\text{ 是非桥}),\qquad
d(v)-2\leq\sum_{e\ni v}q_e .
$$

这些结论在 Lean 中都从实际生成树导出。令 $B=\{v:d(v)>2\}$。因为 $B$ 中的顶点两两不相邻，每条边在 $B$ 的关联边和中至多出现一次。因此

$$
\sum_{v\in B}(d(v)-2)\leq\beta.
$$

等号成立时，每条非桥都必须有一个端点在 $B$。否则它正的省略概率将被整个漏掉。设 $\ell$ 是叶子数，对任意至少有两个顶点的连通图，握手公式又给出左端为 $2\beta-2+\ell$。所以 **$\beta+\ell\leq 2$**。

考虑最小度至少 2、且没有桥的连通图，这涵盖至少三顶点的双连通图。若 $B$ 为空，图就是一个环。若 $B$ 非空，则 $\ell=0$ 且 $2\beta-2>0$，因此 $\beta=2$，前面的不等式取等号。每条边都有且仅有一个端点属于 $B$，而 $B$ 中顶点的总超额度为 2。在 $B$ 之外取一个与分支点相邻的顶点，它的度是 2，因此有两个不同的邻点属于 $B$。这迫使 $B$ 恰有两个顶点，而且它们的度都是 3。其余各点都连接这两个顶点，它们恰有三个，故 $G=K_{2,3}$。

路径与环中的任何生成树都满足所需的度上界。对于 $K_{2,3}$，取生成树的均匀分布。每棵树的四条边各有一个端点在二点侧，所以两个分支点的树中度数之和恒为 4。交换这两点给出生成树集合的一个双射，故两者期望度都是 2。三点侧各点本来的度已经是 2。对于非双连通的情况，Devriendt 已在命题 3.7 证明任何这样的 RN 图都必须是路径。结合此命题就得到全部连通图的分类。$K_{2,3}$ 本身的 RN 性也已由 Devriendt 对 $K_{k,k+1}$ 的统一结果给出；这里补上它在此类图中的唯一性及生成树的机器证明。[Devriendt，命题 3.7、定理 3.8 和完全二部图的例子](https://link.springer.com/article/10.1007/s00026-025-00774-x)

**一个细分推论。** 如果把某个连通简单图的每条边都替换为长度至少 2 的路径，并令这些路径的内部顶点互不相交，所得图一定是 2-sparse。它也没有四边形，因为细分后的每条环都来自原图的一条环，长度至少为 6。因此整个细分图是 RN 当且仅当原图是路径或环。比如任取一个有分支点的双连通平面简单图，将每条边一分为二后，任何正电导赋值都会在某处产生负电阻曲率。

## Lean 覆盖与复验

`SparseResistance.lean` 使用 Lean 4.24.0 / mathlib v4.24.0。图类型是 mathlib 的 `SimpleGraph`。代码枚举同一顶点集上满足 `T ≤ G ∧ T.IsTree` 的所有图作为生成树，并以严格正、归一化的实数权重刻画生成树分布。核心的充要定理涵盖连通、最小度至少 2 且没有桥的图，无需专设平面性。由“非双连通 RN 图必为路径”推出全连通分类的一步引用原论文命题 3.7；Lean 文件直接证明的是前述无桥分类、路径充分性和以下计数结论。电导语言的等价性引用原论文定理 3.8。

| Lean 定理 | 内容 |
|---|---|
| `omissions_of_RN` | 从生成树概率得到省略边的总量及非桥上的严格正性 |
| `branch_excess_le_cycle_rank` | 分支点超额度之和至多为圈秩 |
| `edges_add_leaves_le_vertices_add_one` | 对非平凡连通图，$\beta+\ell\le 2$ |
| `rn_of_degree_le_two` | 最大度不超过 2 时的充分性 |
| `rn_of_K23Shape` | 对称性及 $K_{2,3}$ 的充分性 |
| `rn_iff_degree_le_two_or_K23` | 主分类的无桥、最小度至少 2 情形 |
| `squareFree_rn_iff_degree_le_two` | 在相同条件下，无四边形时 RN 当且仅当图的最大度不超过 2 |

将文件置于相应版本的 mathlib 工作区，执行以下命令。七个公理审计均只列出标准的 `propext`、`Classical.choice` 和 `Quot.sound`，完整输出在 `lean-check.txt`。

```sh
lake env lean SparseResistance.lean
python3 check_sparse_resistance.py
```

独立脚本用 Python 标准库遍历至多六顶点的每个带标号连通 2-sparse 图，逐棵枚举其生成树。肯定结果由均匀分布认证。否定结果则通过寻找顶点子集 $S$，检验每棵树中 $S$ 的总超额度均非负，并至少有一棵树严格为正。这为所有满支撑分布给出整数反证。共检查 4,060 张图，其中 437 条路径、76 个环、10 个带标号的 $K_{2,3}$ 和 3,537 个被排除的图。

## 公开先例核查

核查日期为 2026-11-27。除题号、作者、论文号外，还检索了 2-sparse、独立分支点、theta 图、完整细分、无弦图、二循环图和等价的生成树期望度约束。记录以下与范围或创新性最接近的结果。

- Garcia 的证明限制了严格 RN 图的二部结构，其 Question 6.1 仍要求给出结构描述。Agrahari 等研究韧度、不可迹图与笛卡尔积。Guo、Sun、Yang 给出多项式时间判定、格图分类，在结尾仍列出双连通平面图的结构分类问题。Wang 给出分数 Hamilton 性与正曲率的充分条件。[Garcia](https://arxiv.org/abs/2609.23394) · [Agrahari 等](https://arxiv.org/abs/2607.13169) · [Guo、Sun、Yang](https://arxiv.org/html/2608.20778v1#S5) · [Wang](https://arxiv.org/abs/2609.03412)
- Devriendt 和 Garcia 的研究主页指向上述论文。Agrahari 团队的公开代码仓库提供逐图判定算法及特殊图证书。截至核查时，GitHub API 列出单一 `main` 分支，提交 `f2b89cb3a7ab662b6ec813af88985e872aabf6e8`，无历史 PR、无公共 fork。目录包含线性规划、韧度计算、例图及验证程序。公开材料中未定位到这项 2-sparse 结构分类。[Devriendt 主页](https://sites.google.com/view/kareldevriendt/research) · [Garcia 主页](https://haileyjay.net/) · [作者代码快照](https://github.com/Gyagr7/Effective-Resistance-Curvature-Graph-Properties/tree/f2b89cb3a7ab662b6ec813af88985e872aabf6e8)
- GitHub Code 的精确组合命中一份资讯归档，两组词出现在不同条目。两项 AI 公开项目的代码及 Issues 亦经检索。TrureTuring 有两条登记引用笛卡尔积上的电阻曲率论文，登记目标均为有向拉普拉斯谱宽问题。solved-conjectures 与 MColbrook/AIM 的公开目录中未定位到同题证明。[TrureTuring #21873](https://github.com/the-omega-institute/trureturing/issues/21873) · [#21874](https://github.com/the-omega-institute/trureturing/issues/21874) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures) · [AIM 目录](https://github.com/MColbrook/AIM/blob/main/CATALOG.md)
- MathDB 的原页 #365230 是电阻容量次模性，#362122 是乘积图顶点曲率的符号，#405254 列出韧度与分数 Hamilton 性的进展。三页的解答区均显示 0 条。按作者、两项宽问题及图类检索，没有定位到本分类的独立原页。公开检索的结果不能确证全网或未发表材料中的优先权。[MathDB #365230](https://mathdb.com/p/365230/submodularity-characterization-of-resistance-nonnegativity) · [#362122](https://mathdb.com/p/362122/negative-curvature-from-nonpositive-factors-in-cartesian-gra) · [#405254](https://mathdb.com/p/405254/scheinerman-ullman-fractional-hamiltonicity-conjecture-and-d)

另查到两份实际的 AI 解答，分别反驳 Devriendt 的两个次模性猜想和另一组作者的乘积图曲率猜想。这两个不同问题的 MathDB 页面都显示零条解答。本文比较的 2-sparse 分类没有出现在这两份论证中。[Nowicki/Eve 的次模性反例](https://zenodo.org/records/23401221) · [乘积图反例和证书](https://huggingface.co/datasets/PureOne/iuno-cartesian-curvature-counterexamples)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Combinatorics.SimpleGraph.Bipartite Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true SparseResistance.lean
```
