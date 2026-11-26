# 非回溯随机游走严格缩短平稳起点到每个目标的平均命中时间

Breen、Kempton、Knudson、Shumway 在 2025 年预印本第 5 节 Question 4 中猜测，以**顶点首次命中时间**定义的非回溯 Kemeny 常数严格小于普通随机游走的 Kemeny 常数。本文给出肯定答案，并证明在按平稳分布随机选择目标之前，每个固定目标已经满足严格不等式。[原论文，第 5 节 Question 4](https://arxiv.org/html/2510.06650v1#S5) · [作者原始预印本](https://arxiv.org/abs/2510.06650)

## 结论和适用范围

设 $G$ 为非空有限无向简单图，顶点 $i$ 的度为 $d_i\ge2$。普通游走每一步在全部邻点中均匀选择。非回溯游走的第一步也在全部邻点中均匀选择，此后从候选邻点中删去刚离开的顶点。令 $\pi_i=d_i/\sum_jd_j$，并令 $M^{\mathrm{NB}}_{it},M^{\mathrm{S}}_{it}$ 为从 $i$ 首次命中 $t$ 的期望步数，起点即目标时取零。

对每个目标 $t$，只要两种游走从每个起点到 $t$ 的均值有限，就有

$$
\sum_i \pi_i M^{\mathrm{NB}}_{it}<\sum_i \pi_i M^{\mathrm{S}}_{it}.
$$

再按 $\pi_t$ 对目标求和，得到原题的 $\pi^\top M^{\mathrm{NB}}\pi<K(G)$。普通游走满足经典的随机目标恒等式，$\pi^\top M^{\mathrm{S}}\pi=K(G)$。原文的 Question 4 明确限定在这些量有定义的图上。Lean 将其写为每个新起点的截断均值有界，并定义实际均值为这些截断均值的上确界。[原文对两种常数和第一步的定义](https://arxiv.org/pdf/2510.06650#page=5)

## 差值的精确公式

固定 $t$。记 $y_i=M^{\mathrm{S}}_{it}$、$x_i=M^{\mathrm{NB}}_{it}$。对每对邻点 $i,j$，记 $a_{ij}$ 为非回溯游走**当前在 $i$、上一步在 $j$** 时到 $t$ 的剩余期望步数。令

$$
F_{ij}=y_i-y_j,\qquad J_{ij}=a_{ij}-a_{ji},\qquad
c_i=\begin{cases}1/d_i&i\ne t,\\0&i=t,\end{cases}
\qquad R_{ij}=1-c_i-c_j.
$$

将两种游走的差写成平方和可得

$$
2\sum_i d_i(y_i-x_i)=
\sum_{i\sim j}^{\mathrm{or}}R_{ij}(F_{ij}-J_{ij})^2+
2\sum_{i\sim j}^{\mathrm{or}}c_i(F_{ij}-1)^2.
$$

标记 $\mathrm{or}$ 表示每条无向边的两个方向各算一次。$d_i\ge2$ 保证 $R_{ij}\ge0$，其中也允许零电阻。第二项严格为正。取 $t$ 的一个邻点 $i$，再取 $i$ 除 $t$ 以外的邻点 $j$。两端均为非目标顶点，$c_i,c_j>0$；而 $F_{ij}=-F_{ji}$，这两个方向不可能同时为 $1$。

公式由首次命中的一步递推导出。对 $i\ne t$ 有

$$
d_i x_i=d_i+\sum_{j\sim i}a_{ji},\qquad
(d_i-1)a_{ij}=d_i-1+\sum_{\ell\sim i}a_{\ell i}-a_{ji}.
$$

将第二式对 $j$ 求和，可得 $\sum_j J_{ij}=d_i$。普通游走的递推同样给出 $\sum_j F_{ij}=d_i$。令 $u_i=x_i-c_i$，逐边相减得到 $R_{ij}J_{ij}=u_i-u_j$。对任一反对称流 $L$，有限图的分部求和给出 $\sum_{ij}^{\mathrm{or}}(u_i-u_j)L_{ij}=2\sum_i u_i\sum_{j\sim i}L_{ij}$。分别代入 $F,J$，利用 $u_t=0$ 和二者相同的非目标散度，展开 $(F-J)^2$ 与 $(F-1)^2$ 即得公式。

在 $n$ 个顶点的环上，到固定目标的平稳起点平均时间分别为 $(n-1)/2$ 和 $(n^2-1)/6$，差为 $(n-1)(n-2)/6$。这个例子同时说明，即使内边电阻为零，仍然存在严格改进。

## Lean 与独立复验

`NonbacktrackingKemeny.lean` 从实际允许的下一跳定义截断首次命中时间和逐步生存概率，证明

$$
\mathbb E[\min(T,n)]=\sum_{r=0}^{n-1}\Pr(T>r).
$$

在均值有界时，代码对有限邻居和取极限，给出处理目标、第一步和带方向边的全部方程。`FirstStep.energy_gap` 形式化精确差值，`stationary_target_strict` 和 `kemeny_nonbacktracking_lt_simple` 直接作用于上述游走的均值。`lean-check.txt` 列出的五项审计只使用 `propext`、`Classical.choice` 和 `Quot.sound`。

独立包已锁定 Lean 与 mathlib 版本。进入包目录运行。

```sh
lake exe cache get Mathlib.Analysis.SpecificLimits.Basic Mathlib.Topology.Algebra.InfiniteSum.Real Mathlib.Data.Finset.Card Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true NonbacktrackingKemeny.lean
python3 check_kemeny.py
```

独立 Python 程序按有向边建立吸收方程，用有理数高斯消元直接求值。它遍历 3 至 5 个带标号顶点、最小度至少为 2 的全部 264 个图，对 1,308 个固定目标核对严格不等式及平方和恒等式。另外检查四个环长度，以及两个三角形用桥边相连的图。后者六个目标的平稳均值改进依次为 $869/168,869/168,11/7,11/7,869/168,869/168$。

## 在先结果核查

截至 2026-11-27，公开检索使用精确题号、论文号、作者，以及 `stationary-source first hitting time`、`vertex-space Kemeny`、`non-backtracking commute time`、有效电阻与吸收链等表述。以下工作与本题最接近。

- Fasino、Tonetto、Tudisco 研究二阶游走的首次命中时间及回返时间，给出一阶提升与计算方法。Breen 等 2022 年工作比较的是以**有向边为目标**的 Kemeny 常数，在一些图上有例外。Neal 研究减小回溯后的 MCMC **渐近方差**。此次核查未在这些工作找到本题按顶点首次命中的严格比较。[二阶首次命中论文](https://arxiv.org/abs/2105.14438) · [有向边常数](https://arxiv.org/abs/2203.12049) · [Neal 的渐近方差定理](https://arxiv.org/abs/math/0407281)
- 原作者的 GitHub 仓库提供非回溯计算程序。TrureTuring 的两份问题登记引用本题原论文，登记的结论是另一篇论文中的有向图拉普拉斯谱宽猜想。对 TrureTuring 和 solved-conjectures 的代码及 Issues 检索未发现 Question 4 的证明。[原作者代码](https://github.com/mwshumway/NBRW) · [TrureTuring 检索命中之一](https://github.com/the-omega-institute/trureturing/issues/21873) · [第二份登记](https://github.com/the-omega-institute/trureturing/issues/21874) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures)
- Hugging Face 上有 AI 署名的工作给出顶点非回溯 Kemeny 常数可达三次增长的图族，明确针对同文 **Question 5**。MathDB 定向检索找到的邻近 #381212 询问两个独立游走的相遇时间，其原页有另一问题的反例。本次没有定位到 Question 4 的 MathDB 原页。公开检索不能排除未收录或未发表的先例。[Question 5 的公开稿](https://huggingface.co/datasets/PureOne/evie-cubic-nonbacktracking-kemeny) · [MathDB #381212](https://mathdb.com/p/381212/expected-meeting-time-conjecture-for-random-walks-on-regular)
