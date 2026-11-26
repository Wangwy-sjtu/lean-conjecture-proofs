# Levin 的 Band or Bump 停牌猜想

**对任意牌型数和全部合法阈值，首次因 bump 停牌的概率随抽牌时刻对数凹。** 设有 $m$ 种牌、每类 $s$ 张，$1\le\ell\le u<s$。当 $m\ge2$，概率为正的时刻恰为 $u+1\le n\le(m-1)u+\ell$。零下限、零上限、上限等于每类牌数及单一牌型均已纳入。一般证明从带标号牌的实际停时出发，并给出 1,071 组精确复核。[完整数学证明](README-all.md) · [一般 Lean 定理](BandOrBumpAll.lean) · [原文 Remark 2](https://arxiv.org/pdf/2407.08062#page=7)

三种和四种牌型另有较短的证明。下面保留三牌型的两个上界论证，四牌型使用三次多项式分解。[四牌型短证明](README-four.md)

## 三牌型的两上界证明


Bruce Levin 在《The Game of Band or Bump》的 Remark 2 提出猜想。将一副有 $m$ 种牌型、每种 $s$ 张的牌洗匀后逐张抽取。当每类累计数都位于 $[\ell,u]$ 时出现 band，当某类累计数首次达到 $u+1$ 时出现 bump，两者中先发生的事件结束游戏。记 $N$ 为停止时刻，$p_n=\Pr(N=n,\mathrm{bump})$。Levin 已证明 band 一侧的联合概率对数凹，并在论文第 7 页根据数值结果猜想 bump 一侧也对数凹。 [arXiv 论文与版本记录](https://arxiv.org/abs/2407.08062) · [第 7 页，Remark 2](https://arxiv.org/pdf/2407.08062#page=7) · [哥伦比亚大学技术报告 B-256](https://www.columbia.edu/~bl6/appendices/Tech%20Report%20B-256%20The%20Game%20of%20Band%20or%20Bump.pdf)

**已证情形。** 取 $m=3$。对每个 $1\le\ell\le u<s$ 及每个 $n\ge0$，有

$$p_np_{n+2}\le p_{n+1}^{\,2},\qquad
p_n>0\ \Longleftrightarrow\ u+1\le n\le 2u+\ell.$$

这包括论文写出的整个考察区间 $3\ell\le n\le 2u+\ell$，也包括较早的抽牌时刻，因而给出了原文所要求的对数凹性和连续支集。牌数及两个阈值均可任意增长。任意牌型数的结论见同包的一般证明。

## 为什么三种牌型可以证明

在第 $n$ 张处固定一张具体的标号牌。此前的 $n-1$ 张作为无序手牌，均匀取自其余 $3s-1$ 张。任何一张牌都可通过牌型及标号的置换变为这张固定牌，因此这个条件下的 bump 概率等于原游戏的联合概率。

设固定牌属于第一型。要在这一抽首次以 bump 停止，前面必须恰有 $u$ 张第一型牌。另两型的数量 $i,j$ 要求 $i,j\le u$、$\min(i,j)<\ell$。最后一个条件保证此前每一步都有一类不足 $\ell$；各类累计数单调，所以此前也不会越过 $u$。反过来，若前一刻各类都不超过 $u$ 且两类都已达到 $\ell$，此时已经出现 band。令 $k=n-u-1$，便得到

$$p_n=\frac{\binom{s-1}{u}}{\binom{3s-1}{u+k}}
\sum_{\substack{i+j=k,\,0\le i,j\le u\\\min(i,j)<\ell}}
\binom{s}{i}\binom{s}{j}.$$

记 $R_k(a,b)$ 为上式只要求 $i\le a,j\le b$ 的质量，保留相同的分母及第一型因子。它有一个现成的概率解释：在 $s-1,s,s$ 三类牌中抽取 $u+k$ 张，使各类数目落入矩形 $\{u\}\times[0,a]\times[0,b]$ 的概率。Levin 独立发表的矩形概率定理给出 $R_k(a,b)$ 关于样本大小的对数凹性。 [Levin，*Sequential Analysis* 43 (2024), 417–431](https://doi.org/10.1080/07474946.2024.2379901)

在每个 $k\ge0$ 都有两个上界 $p_{u+1+k}\le R_k(u,u)$ 及 $p_{u+1+k}\le 2R_k(\ell-1,u)$。后者来自对哪一类不足 $\ell$ 分别计数，再用对称性。若 $k<2\ell$，两类不可能同时达到 $\ell$，第一个上界恰好取等。若 $k>2(\ell-1)$，两类不可能同时不足 $\ell$，第二个上界恰好取等。这两个范围覆盖所有整数 $k$。在任一中央指标选取在那里取等的上界，其两个邻项也覆盖目标概率的两个邻项，相乘便得到所求的不等式。等价地，目标序列是这两个对数凹上界逐项的最小值。

当 $0\le k\le u+\ell-1$ 时，取 $i=\min(u,k)$ 和 $j=k-i$ 就产生正权重。若 $k>u+\ell-1$，一个计数最多为 $u$、另一个最多为 $\ell-1$ 的要求不能满足。这给出完整支集。

## Lean 中验证的对象

[BandOrBump.lean](BandOrBump.lean) 把固定最后一张后的牌堆定义为三个有限类型的不交并，以所有等大小标号子集为分母，用实际手牌组成的有限集作分子。`count_hands` 将这些子集按各牌型数目不交分组，推导上式。`bump_hand_iff_first_bump` 从逐前缀的规则推出相同的停止判据。时间 $n=0$ 及牌堆用尽之后均按零质量处理。

| Lean 声明 | 内容 |
| --- | --- |
| `BandOrBump.three_ranks_bump_log_concave` | 每个抽牌时刻均满足相邻三项的不等式 |
| `BandOrBump.three_ranks_support` | 精确的正概率区间 |
| `BandOrBump.bump_hand_iff_first_bump` | 对符合标号手牌计数的每种排列，停止判据与手牌成员资格等价 |

Lean 也从二项式恒等式证明了实际使用的矩形概率定理。具体地，设 $A_k=\sum_{i+j=k,i\le a,j\le b}\binom si\binom sj$。从一个合法的 $k$ 张手牌再加入一张时，若某类已达到上限，将损失一批扩展，记损失总数为 $E_k$。双计数得到 $(k+1)A_{k+1}=(2s-k)A_k-E_k$。二项系数的相邻比递减，对每一项分别比较得到 $E_kA_{k+1}\le E_{k+1}A_k$。对任意 $T\ge2s+u$，在相邻非零项间，$A_k/\binom{T}{u+k}$ 的增长比是两个非负递减因子的积

$$\left(1+\frac{u}{k+1}\right)
\left(1-\frac{T-u-2s+E_k/A_k}{T-u-k}\right).$$

取 $T=3s-1$ 即得本题所需的矩形结论。该证明覆盖 $a=0$ 或 $b=0$ 的情形，并在各支集端点直接验证相邻不等式。

## 复验

三个主声明的内核公理均为 `propext`、`Classical.choice`、`Quot.sound`。[内核输出](lean-check.txt) · [独立顺序抽牌核查](check_game.py)

核查程序直接按剩余牌的张数推进条件概率，遇到 band 或 bump 便停止。对 $2\le s\le9$ 的全部 120 组合法参数，每个时刻的精确有理概率均与公式一致。例如 $s=5,\ell=2,u=3$ 时，$p_4,\ldots,p_8$ 依次为 $1/91,40/1001,90/1001,160/1001,50/429$。

## 公开先例核查

截至 2026 年 11 月 27 日，按题名、arXiv 编号、作者、`Book or Band`、`bump stopping time`、`three ranks`、`log-concavity`、多元超几何矩形概率及其并集等表述查阅公开结果。最接近的正式结果是 Levin 的矩形概率定理，原作者在提出 bump 猜想时也引用了该定理。原论文给出了联合概率的计算式；其 Remark 2 仍把 bump 的对数凹性列为猜想。未从本次可访问的结果找到先前写出上述三牌型定理或该两上界证明的材料。 [作者的出版目录](https://www.columbia.edu/~bl6/publist.htm) · [arXiv 原记录](https://arxiv.org/abs/2407.08062) · [矩形概率定理](https://doi.org/10.1080/07474946.2024.2379901)

GitHub 全局代码检索中，与论文编号匹配的文件包括 arXiv 索引及 RSS 摘要。对 `1337isnot1337/solved-conjectures` 和 TrureTuring 的代码及 Issues 检索，题名与编号没有返回该定理的证明。用 MathDB 的公开网页索引，以题名、作者加超几何停止时刻、旧游戏名及 arXiv 编号检索，未定位到可确认的题目原页，未取得其订阅数据库快照。公开检索的覆盖范围不能排除未收录或未公开的证明。 [GitHub 的原论文 RSS 存档](https://github.com/ehijano/rss_fetch/blob/2820b6d225aac11cdc3f9e8f0136ff031869cee9/rss_data/stat.AP/2024-07-11_stat.AP.xml) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures) · [TrureTuring](https://github.com/the-omega-institute/trureturing) · [MathDB 公开数据库](https://mathdb.com/database)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Fintype.Sum Mathlib.Data.Fintype.Powerset Mathlib.Data.Finset.Sum Mathlib.Data.Finset.Prod Mathlib.Algebra.BigOperators.NatAntidiagonal Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring Mathlib.Logic.Equiv.Fin.Basic Mathlib.Data.Fintype.Prod Mathlib.Algebra.Polynomial.Derivative Mathlib.Algebra.Polynomial.BigOperators Mathlib.Tactic.LinearCombination
lake build BandOrBumpAll
lake env lean -DwarningAsError=true BandOrBumpAll.lean
lake env lean -DwarningAsError=true BandOrBump.lean
lake env lean -DwarningAsError=true BandOrBumpFour.lean
python3 check_game.py
python3 check_four_game.py
python3 check_all_ranks.py
```
