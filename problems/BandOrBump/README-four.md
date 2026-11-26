# 四种牌型的 Band or Bump 猜想

对每种牌型各有 $s$ 张的四牌型牌堆，以 $1\le\ell\le u<s$ 为两道阈值。抽牌至各型计数同时属于 $[\ell,u]$，或有一类首次达到 $u+1$。令 $p_n$ 为后者在第 $n$ 张率先发生的联合概率。对所有非负整数 $n$，已经证明

$$p_n p_{n+2}\le p_{n+1}^2,\qquad p_n>0\ \Longleftrightarrow\ u+1\le n\le3u+\ell.$$

这是 Bruce Levin 对 bump 概率提出的猜想的四牌型情形，包含作者 Table 1 用标准 52 张牌、四花色、$\ell=5,u=8$ 的例子。同包另有覆盖任意牌型数的证明。[全部牌型数](README-all.md) [原论文，Remark 2 与 Table 1](https://arxiv.org/pdf/2407.08062) · [作者的技术报告](https://www.columbia.edu/~bl6/appendices/Tech%20Report%20B-256%20The%20Game%20of%20Band%20or%20Bump.pdf)

## 证明

固定第 $n$ 张抽出的具体标号牌。在剩下的 $4s-1$ 张牌中，前 $n-1$ 张是均匀抽取的无序子集。置换牌型和同型牌的标号能在任意两张被固定的牌之间建立双射，因此每张最后牌对应相同的条件概率。在它之前要恰好有 $u$ 张同型牌，另三型各至多有 $u$ 张，而且至少一类不足 $\ell$。这些条件保证每个此前前缀没有出现 band 或 bump。反之，此前没有停止且末张造成 bump，必满足这几条计数约束。

对未被指定的牌型，定义三个计数多项式

$$L(x)=\sum_{i=0}^{\ell-1}\binom si x^i,\qquad G(x)=\sum_{i=\ell}^{u}\binom si x^i,\qquad F(x)=L(x)+G(x).$$

令 $k=n-1-u$。分母为 $\binom{4s-1}{n-1}$，分子为 $\binom{s-1}{u}[x^k](F^3-G^3)$。有两段分别成立的矩形公式。

1. 若 $k<3\ell$，$G^3$ 在 $k$ 次项为零，目标质量等于由 $F^3$ 给出的矩形概率。这个矩形在所有指标都是目标的上界。因此，若中央指标满足这个条件，将两邻项放大到矩形概率，便得到所需的对数凹不等式。
2. 由 $F=G+L$ 得 $F^3-G^3=3LFG+L^3$。$L^3$ 的次数最多是 $3\ell-3$。当中央指标 $k\ge 3\ell$ 时，$k-1,k,k+1$ 的三个系数都来自同一个多项式 $3LFG$。一类取低计数、一类只取上界、一类取高计数，正构成一个矩形，故这三项也满足对数凹不等式。

上述矩形还包括固定末牌类型的精确计数 $u$。已有矩形概率定理对各牌型的不同大小与上下限都适用。区间 $0\le k\le 2u+\ell-1$ 中，允许两类各至多 $u$、第三类至多 $\ell-1$ 时能构成每个整数总数，超出上界则不可能。这给出 $p_n$ 的连续正支集。 [Levin 的多元超几何矩形定理](https://doi.org/10.1080/07474946.2024.2379901)

## Lean 核查的范围

[BandOrBumpFour.lean](BandOrBumpFour.lean) 对每个牌型使用实际标号牌子集 `Finset (Fin s)`，随后用四个子集组成抽牌前的一手牌。`bumpHands` 在各类均未越过上限的牌手中，删去另三类已经全部达到下限的牌手。它的基数除以同大小均匀牌手总数，定义了 `bumpProbability`。`inventory_coeff` 和 `count4` 直接把标号牌手的计数等同于多项式系数。`bump_hand_iff_first_bump` 则对同一手牌的每一种次序，验证了逐前缀游戏规则。第一张以前及牌堆用尽以后的联合概率都为零。

| 定理 | 结论 |
| --- | --- |
| `FourRankBump.four_ranks_bump_log_concave` | 全部四牌型游戏、全部抽牌时刻的对数凹性 |
| `FourRankBump.four_ranks_support` | 正概率支集恰为 $[u+1,3u+\ell]$ |
| `FourRankBump.bump_hand_iff_first_bump` | 真正停时规则与标号牌手筛选的等价性 |
| `BandRect.Box.log_concave` | 各牌型任选不同比例、任意上下限时，矩形事件的概率关于样本大小对数凹 |

矩形部分在文献中已有定理。文件从二项系数及有限求和独立推导这一工具。对总容量 $S$ 的一个矩形，令 $a_k$ 为其中 $k$ 张牌手数。令 $h_k$ 为从这种牌手再抽一张时会越过类型上界的全部扩展数；令 $d_k$ 为从这种牌手抽去一张时会越过类型下界的选择数。双计数给出

$$(k+1)a_{k+1}-d_{k+1}=(S-k)a_k-h_k.$$

在正支集内，$h_k/a_k$ 递增，$d_k/a_k$ 递减。文件先从区间截断二项系数证明这些边界性质，再利用卷积保持二阶全正性和似然比序，把性质推广到任意有限个牌型。这样就能比较 $a_k/\binom Sk$ 的相邻比。`BandRect.rectangle` 接受任意非空有限牌型列表。

## 复验与标准牌局

在本下载包的目录中，按主说明准备锁定的 mathlib 依赖，再执行

```sh
lake env lean -DwarningAsError=true BandOrBumpFour.lean
python3 check_four_game.py
```

四项定理仅使用 `propext`、`Classical.choice` 和 `Quot.sound`。[内核输出](lean-check-four.txt) · [独立逐张抽牌程序](check_four_game.py)

程序以未抽牌数给定下一花色的精确条件概率，遇到任一规则即停止。它逐时刻核对了 $2\le s\le9$ 的全部 120 组参数，另核对了作者的标准牌局。标准牌局的总 bump 概率为 $532134081359/1350540667070$。其中 $p_9=1/1286390$，$p_{24}=3941606097/69784776110$，$p_{29}=23449215933/2623907581736$，与 Table 1 对应的小数一致。[原文 Table 1](https://arxiv.org/pdf/2407.08062#page=2)

## 公开先例

截至 2026 年 11 月 27 日，按 arXiv 编号、游戏新旧名称、作者、标准四花色例子、三次多项式差、未达到全部优惠券配额的停止时刻及超几何样本矩形等检索。最接近的正式材料是原文的单组标准牌数值表和作者的任意矩形定理。公开可检索的 arXiv、GitHub、TrureTuring 与 MathDB 结果中没有定位到四牌型全部阈值的证明；MathDB 未找到能确认对应此题的原页。GitHub 中有原论文 RSS 或标识符镜像，两个 AI 解题库的定向代码及 Issues 检索未返回此结论。覆盖范围限于所查公开资料。[作者的论文目录](https://www.columbia.edu/~bl6/publist.htm) · [公开摘要镜像](https://github.com/ehijano/rss_fetch/blob/2820b6d225aac11cdc3f9e8f0136ff031869cee9/rss_data/stat.AP/2024-07-11_stat.AP.xml) · [TrureTuring](https://github.com/the-omega-institute/trureturing) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures) · [MathDB](https://mathdb.com/database)
