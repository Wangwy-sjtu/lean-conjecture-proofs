# 半受限有向图博弈的平方根误差界

Spiro、Surya、Zeng 在 *Electronic Journal of Combinatorics* 30(4) 的 Question 22 中询问，对任意有限有向图和任意配额，最优期望收益能否控制在最佳固定动作收益加上 $O_D(\sqrt M)$ 之内。**答案是肯定的。限制方把全部配额均匀洗牌、依次出牌，就足以保证这个误差阶。** 原论文定理 3 对一般配额给出了 $O_D(M^{2/3})$。[原论文，Question 22 和定理 3](https://doi.org/10.37236/11563) · [预印本](https://arxiv.org/abs/2207.11272)

设图有 $d\ge1$ 个顶点。限制方 Rei 必须恰好在 $r_u$ 轮中出顶点 $u$。对手 Norman 每轮任选顶点，双方同时出招，然后公开结果和动作。Norman 出 $a$、Rei 出 $u$ 时，他得到 $\mathbf1_{a\to u}-\mathbf1_{u\to a}$ 分。记总轮数为 $N=\sum_u r_u$，$M=\max_u r_u$，并令

$$
B=\max_a\left(\sum_{u\in N^+(a)}r_u-\sum_{u\in N^-(a)}r_u\right).
$$

若 $S_D(r)$ 表示在双方最优策略下 Norman 的期望总分，Lean 验证了

$$
B\;\le\; S_D(r)\;\le\; B+15d\sqrt N\;\le\; B+15d^{3/2}\sqrt M .
$$

常数 15 便于逐轮验证。对有向三环及相等配额 $r=(n,n,n)$，已有结果给出 $B=0$ 且 $S_D(r)\sim 3\sqrt3\,\sqrt n/(2\sqrt\pi)$，从而一般上界的平方根阶无法改善。[Janson，定理 1](https://doi.org/10.37236/12854)

## 均匀洗牌为什么足够

固定动作 $a$ 的总得分只取决于出牌配额。Norman 每轮都出达到 $B$ 的动作，就能无条件得到 $B$，这给出下界。

现在让 Rei 均匀打乱 $N$ 张带标签的牌，每次从剩余牌中等概率出一张。设某轮开始时剩余 $s$ 张，$m_a$ 是此时牌面收益对动作 $a$ 的平均值，$c_a$ 是初始牌组对同一动作的平均值。任意依据历史选出的动作，其当轮条件期望都至多为

$$
\max_a m_a\le\max_a c_a+\sum_a|m_a-c_a|.
$$

剩下的 $s$ 张牌在全局分布中是等概率的 $s$ 元子集。对每个动作，无放回抽样的样本均值标准差至多为 $1/\sqrt s$，因为整副牌的收益都在 $[-1,1]$ 内。再对各轮累加，用 $\sum_{s=1}^N s^{-1/2}\le 2\sqrt N$ 即得到所需阶。这个论证也解释了为何配额可以很不均匀，以及对手为何能够根据此前所有动作调整策略。有限总体的抽样估计是经典工具。[Hoeffding，无放回抽样的估计](https://doi.org/10.1080/01621459.1963.10500830)

## Lean 验证了哪些对象

`SemiRestricted.lean` 从历史依赖策略及每轮的实际抽牌递推定义期望总分。可选的有向边只作为关系传入，收益的两个符号由出边和入边分别确定。每种顶点 $u$ 具体展开为 $r_u$ 张独立编号的牌，公开动作只揭示顶点类型。均匀策略的界甚至允许对手看到此前抽出的每张牌的编号。限制方的极小极大上值定义为其所有可保证上界的下确界，固定动作和合法洗牌策略分别给出下界和上界。

形式证明用逐轮递推控制有限总体方差。若当前剩 $s+1$ 张牌，某个动作的当前均值为 $m$，新抽出的收益为 $X$，下一轮均值为 $m+(m-X)/s$。由于 $\mathbb E(m-X)=0$ 且 $|m-X|\le2$，对任意常数 $c$ 有

$$
\mathbb E[(m_{\mathrm{next}}-c)^2]\le (m-c)^2+4/s^2.
$$

对剩余 $s$ 张牌和一个动作使用上界项 $s\sqrt s\,(m-c)^2+15\sqrt s$，可以同时支付本轮偏差 $|m-c|$ 和抽牌产生的均方变化。取 $c$ 为该动作的初始牌组均值，所有平方项起初都为零。逐个动作相加，便得到文件中对所有有限有界收益矩阵成立的 $15d\sqrt N$ 界。$N=0$ 也包括在内。

| 定理 | 核验内容 |
|---|---|
| `uniformly_shuffled_score_le` | 逐张无放回均匀抽取能对抗所有历史依赖的随机对手 |
| `matrix_game_sandwich` | 任意 $[-1,1]$ 收益矩阵及任意公开牌型映射的极小极大上下界 |
| `question22` | 有向图、原论文的出入邻域、任意配额以及 $O_D(\sqrt M)$ |

在 Lean / mathlib 4.24.0 的工作区内执行以下命令。三个定理均仅依赖标准的 `propext`、`Classical.choice`、`Quot.sound`。文件 `lean-check.txt` 记录了原始输出。

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Group.Finset.Sigma Mathlib.Data.Real.Sqrt Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true SemiRestricted.lean
python3 check_restricted.py
```

独立的 Python 脚本只使用标准库，通过牌型配额的动态规划计算均匀策略的最坏收益，并在至多三顶点时再用有理数线性规划逐状态求出真实博弈值。共核查 60,829 个有向图与配额组合，其中 1,780 个进行了精确极小极大核查。每条无向顶点对分别取正向、反向或缺边；两方向同时存在时收益与缺边相同。

## 公开先例核查

截至 2026-11-27，查找范围覆盖论文题目、arXiv 和 DOI、作者、Question 22、原式、任意配额的有向图博弈，以及等价的随机多重集洗牌、无放回抽样和自适应收益比较。

- 原论文给出一般配额的 $M^{2/3}$ 误差，并在 Question 22 明确要求 $M^{1/2}$。OpenAlex 所列的正式期刊论文前向引用有一篇，即 Janson 对同文 Question 21 的精确渐近常数及分布研究。Spiro 的公开研究列表也指向原问题。按题名查 GitHub 仓库没有定位到作者维护的配套仓库。[原文](https://doi.org/10.37236/11563) · [作者研究目录](https://mathweb.ucsd.edu/~sspiro/Research/) · [OpenAlex 正式论文记录](https://openalex.org/W4389209584) · [Janson](https://arxiv.org/abs/2402.14676)
- 完整反馈猜牌和固定牌堆的最优预测已有专门研究。Diaconis–Graham 研究命中牌型的顺序猜测。一般收益矩阵与预算受限对手也见于 Abernethy 等人的重复博弈，其预算被耗尽时停止。这里限制方必须用完每个动作的指定次数。此前的概率引理**可以直接用于本题**：选择均匀洗牌后，对每个动作在每个剩余轮数应用经典有限总体方差或 Hoeffding 的无放回界，再对各轮求和，就给出 Question 22 所问的阶。所核查的文献中未定位到将这一推论写成该文 Question 22 答案的先例。[Diaconis–Graham](https://gwern.net/doc/reinforcement-learning/exploration/1981-diaconis.pdf) · [完整反馈猜牌论文](https://www.sciencedirect.com/science/article/pii/S0196885823000878) · [预算受限的重复博弈](https://mwarmuth.bitbucket.io/pubs/C86.pdf) · [Hoeffding](https://doi.org/10.1080/01621459.1963.10500830)
- 按论文号、准确题名和误差界检索 GitHub Code、Issues、TrureTuring、solved-conjectures、MColbrook/AIM、Hugging Face、Zenodo 和 Hexagon，未定位到 Question 22 的在先公开解答。MathDB 的博弈论目录有多项石头剪刀布问题，例如原页 #371528 问多玩家单轮博弈中均衡收益的不平衡，与这里固定配额的多轮机制不同。此次未定位到 Question 22 的 MathDB 原页。公开检索无法证明未收录或未发表的材料中无人解决。[TrureTuring](https://github.com/the-omega-institute/trureturing) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures) · [AIM 目录](https://github.com/MColbrook/AIM/blob/main/CATALOG.md) · [MathDB #371528](https://mathdb.com/p/371528/payoff-imbalance-in-nash-equilibria-of-the-imbalanced-m-2k-1)
- Git 远端当次返回 TrureTuring 的 12,436 个分支名、solved-conjectures 的 13 个与 AIM 的 22 个。检索分支名中的作者、题号、游戏名、猜牌、洗牌、无放回和矩阵收益等词后，又检查了相关候选与通用研究分支的提交或差异。AIM 的 uniform-time-sampling 分支研究无穷观测窗口的采样，solved-conjectures 的 research 分支头是三部图彩色圈，audit 分支头复查七项撤稿。TrureTuring 的 fresh-name-guess 与 Karp 两个近似名称也经核对。此项记录覆盖公开分支名及所列候选，并未全文遍历上万个分支。[AIM 采样分支头](https://github.com/MColbrook/AIM/commit/03aa46d76c9ce6ca7266304563740ea3f9050036) · [solved-conjectures 研究分支头](https://github.com/1337isnot1337/solved-conjectures/commit/0d48ee548254e41efed9de57ae3f620581e74783) · [TrureTuring 候选分支头](https://github.com/the-omega-institute/trureturing/commit/9d7bd9026c8e7b2d31d4f461f442603042bbc721)
