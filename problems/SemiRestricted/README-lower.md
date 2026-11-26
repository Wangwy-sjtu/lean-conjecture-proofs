# 所有含边欧拉有向图的半受限博弈都有平方根收益

Spiro、Surya、Zeng 在 *Electronic Journal of Combinatorics* 30(4), P4.32 的 Question 23 中问，每个至少有一条弧的有限欧拉有向图，是否都让不受配额限制的一方获得 $\Omega_D(\sqrt n)$ 的期望收益。**答案是肯定的。** 设 $d$ 为顶点数，双方每轮同时选择顶点。若 Norman 的顶点指向 Rei 的顶点，他得 1 分，反过来失 1 分。Rei 必须恰好选每个顶点 $n$ 次。令 $S_D(n\mathbf1)$ 为最优期望总分，形式证明确立了

$$
\frac{\sqrt n}{2d}\ \le\ S_D(n\mathbf1)\ \le\ 15d^{3/2}\sqrt n.
$$

论文的 Theorem 2 已给出了这里所需的平方根上界。作者此前的下界要求斜邻接矩阵的核是一维。本证明只用逐顶点入度等于出度，因而包括偶数个顶点的图、二分图、有孤立点的图和不连通的图。原文约定无自环、每对顶点至多一条弧。[原论文，Theorems 2、11 和 Question 23](https://doi.org/10.37236/11563) · [预印本](https://arxiv.org/abs/2207.11272)

## 从有向图中取出一个双牌型博弈

用 $A_{bu}=\mathbf1_{b\to u}-\mathbf1_{u\to b}$ 记单轮收益。每列之和为零。选一条弧的起点 $a$，令 $f(u)=A_{au}$。每种顶点恰好打 $n$ 次，所有 $f(u)$ 之和为零。若 $a$ 的出度为 $k\ge1$，整场一定有 $kn$ 次 $+1$、$kn$ 次 $-1$ 和若干次 $0$。

Norman 可以在看到下一张牌之前，选择任意参数 $-1\le z\le1$，再按照下列概率选顶点 $b$。

$$
q_b(z)=\frac{d-z+dz\,\mathbf1_{b=a}}{d^2}.
$$

这些数非负、和为 1。对每个对手顶点 $u$，这次混合出招的期望收益恰好是 $z f(u)/d$，因为列和为零。Norman 因此既能押正号，又能押负号，还可以连续调整下注幅度。零号牌既没有期望收益，也无需推进下注策略。Rei 可以根据先前全部动作安排零号牌。

令 $X_t$ 为独立等概率正负单位步的 $t$ 步随机游走，定义 $H(t,s)=\mathbb E|s+X_t|$。若还有 $t>0$ 张非零号牌，且历史符号总和为 $s$，就令

$$
z=\frac{H(t-1,s-1)-H(t-1,s+1)}{2}.
$$

绝对值函数的 Lipschitz 常数为 1，故 $|z|\le1$。游走的一步平均公式给出，对 $y=\pm1$ 有 $zy+H(t-1,s+y)=H(t,s)$。对 $y=0$，两边的势相同。这一恒等式适用于每一张可能出的牌。终局的符号总和必为零，$H(0,0)=0$，所以无论 Rei 采用哪种根据历史改变的合法策略，Norman 的预期总收益都精确等于

$$
H(2kn,0)/d.
$$

Lean 还独立证明了 $H(t,0)\ge\sqrt t/2$。具体用到 $\mathbb E X_t^2=t$、$\mathbb E X_t^4=3t^2-2t$。因式分解 $y(y+2c)(y-c)^2\ge0$ 对 $y=|X_t|$ 和 $c=2\sqrt t$ 成立，取期望后即给出这一估计。因此所构造策略实际上达到至少 $\sqrt{2kn}/(2d)$。

## Lean 和精确复验

| 文件或定理 | 核查内容 |
|---|---|
| `SemiRestricted.lean` | 与同组 Question 22 使用的文件逐字相同。定义公开历史策略、合法自适应出牌、逐轮总分及极小极大上值。 |
| `fair_walk_lower` | 任意长度公平符号游走的一阶绝对矩下界。 |
| `balanced_deck` | 对列和为零的任意有限有界收益矩阵，若选中行只取 $0,\pm1$ 且整副牌的行和为零，就有一个公开策略，对所有合法对手恰得 $H(t,0)/d$。 |
| `question23` | 从欧拉图的入出度、弧和统一配额推出上述双边界。 |

三项定理均只依赖 `propext`、`Classical.choice`、`Quot.sound`。项目已锁定依赖，在项目目录中执行

```sh
lake build SemiRestrictedLower
lake env lean -DwarningAsError=true SemiRestrictedLower.lean
python3 check_eulerian.py
```

Python 脚本独立使用二项式公式和有理数，对所有 3–5 个带标签顶点的 234 个非空欧拉有向定向图，以及 4 个 6–8 个顶点的偶环或不连通例子，检查了 1,161 个初始策略收益，以及 108,396 个“此时可能抽到这张牌”的逐步恒等式。它也逐一检查了 $0\le t\le100$ 的游走下界。

## 已核查的公开先例

- 二元平衡序列的最优预测已有长达数十年的研究。Blackwell–Hodges 的 1957 年论文研究等额分配两种处理时，预测下一种处理可得到多少超额命中。Cover 的二元序列预测给出了通过公平符号序列实现末端收益的相应机制。Spiro 的早期论文也求出了多牌型对抗猜牌的最优发牌策略。这里的图论步骤是从每个欧拉有向图中做出上述正负下注，并容许任意交错的零收益牌。二元模型及逐步复制末端收益的方法均有这些先例。[Blackwell–Hodges](https://doi.org/10.1214/aoms/1177706973) · [Cover 的论文原文](https://isl.stanford.edu/~cover/papers/paper3.pdf) · [Spiro，Online Card Games](https://arxiv.org/abs/2106.11866)
- 原论文明确分别列出一维核的 Q23 特例及核并非一维的图族。查原题、正式论文的公开前向引文、作者研究目录、三位作者与 Eulerian digraph、lower bound、matching pennies、selection bias、fixed multiplicities 等组合，定位到 Janson 的有向三环极限常数及分布。检索的一般预算重复博弈论文以预算耗尽为停止准则。截至 2026-11-27，未定位到已写出任意欧拉图 Q23 结论或上述逐列归约的来源。[原文](https://doi.org/10.37236/11563) · [Janson](https://doi.org/10.37236/12854) · [Spiro 的研究目录](https://mathweb.ucsd.edu/~sspiro/Research/) · [原论文的 OpenAlex 期刊记录](https://openalex.org/W4389209584) · [Abernethy–Warmuth](https://mwarmuth.bitbucket.io/pubs/C86.pdf)
- 在 GitHub Code、Issues 和公开 AI 结果中按论文编号、题名、Eulerian 与作者联合查询。solved-conjectures 的目录同时含 Spiro 和 Eulerian，查原文件后分别对应数论中的 Erdős–Granville–Pomerance–Spiro 问题和 Chern–Fu–Lin 的联合欧拉等分布问题。TrureTuring、solved-conjectures、MColbrook/AIM 的远端分别返回 12,436、13、22 个分支名。搜原题与二元游戏等价表述的分支名后，查到一个 Blackwell–Dubins 预测合并定理分支，为另一项定理。这里的检索覆盖各默认分支、分支名及命中候选，没有全文索引全部非默认分支。[solved-conjectures 的目录](https://github.com/1337isnot1337/solved-conjectures/blob/2dfd2a211bb83ca10d33d20eaad608777e74c91d/README.md) · [TrureTuring 的 Blackwell–Dubins 候选提交](https://github.com/the-omega-institute/trureturing/commit/09f8e5bc5eb345363131d8155acc6b70483ff5f5) · [AIM](https://github.com/MColbrook/AIM)
- 另按题名、作者和关键条件检索公开 MathDB、Hugging Face、Zenodo 入口。MathDB 的 #371528 对应多人单轮博弈的均衡收益失衡。没有定位到本题的 MathDB 原页或这些入口中的同题证书。可检索资料的范围无法覆盖未公开或未索引的证明。[MathDB #371528](https://mathdb.com/p/371528/payoff-imbalance-in-nash-equilibria-of-the-imbalanced-m-2k-1)
