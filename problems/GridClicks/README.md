# 所有零空间维数为四的方盘，最坏要按多少次灯？

在标准 Lights Out 方盘上，每按一格就翻转该格和上下左右相邻格。对于一个可解灯态，先求关掉所有灯所需的最少按键次数，再对所有可解灯态取最大，记为 $M(n)$。

**定理。** 若边长 $n$ 的方盘有四维零空间，则有唯一的正奇数 $q=(n+1)/5$，且

$$M(n)=17q^2-10q.$$

这给出 Boyles 在 OEIS A353071 和修订后猜想清单中列出的四维公式。三个例子为 $M(4)=7$、$M(14)=123$、$M(24)=375$。特别地，对每个 $k\ge0$，边长 $5^{k+1}-1$ 的方盘都满足四维条件，故也回答了他关于至少四维的任一无穷族的问题。对一般边长，维数四是定理的实质假设，例如边长 64 对应 $q=13$，其维数是 28。[OEIS 原猜想](https://oeis.org/A353071) · [作者修订稿的猜想与无穷族问题](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L432-L457) · [Lean 主定理](GridClicks.lean)

## 从一个小棋盘得到全体解

若两个按键图案作用后给出同一灯态，它们逐格异或后便是零空间中的图案。四维零空间有 16 个图案，每个可解灯态就有 16 种解。从所有解中找按键最少者，等价于求一个二进制向量到这 16 个图案的最小汉明距离。

边长 $5q-1$ 的方盘可以分成 $q^2$ 个 $4\times4$ 小盘。相邻小盘互为镜像，中间空一行或一列。把同一个小盘零空间图案这样铺到整盘，分隔线上相邻影响成对抵消。这是 Boyles 已用过的镜像铺法。小盘有 16 个不同的图案，首行的 4 个比特即可区分它们。当大盘的零空间也是四维时，这 16 个延拓就是全部零空间。分隔线上共有 $Z=(5q-1)^2-16q^2$ 个格，任一零空间图案在那里都取零。[作者的铺盘论证](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/finite_fields/finite_fields.tex#L365-L395) · [五格翻转、双射和计数](ClickTiles.lean)

**上界。** 记 $t=q^2$，它是奇数。在每个小盘中标出首行第二格，位置按该小盘的镜像方向读取。将 16 个图案按标记格的值分成两组，每组 8 个。直接写出 16 个小盘图案可见，在任一组中，其余 15 格都各有 4 个图案取 0、4 个取 1。对任意给定的按键向量，选标记格多数相同的那一组。把它到组内 8 个图案的距离相加，其余格恰贡献 $60t$，标记格最多贡献 $8(t-1)/2$。故至少有一份解在小盘内的代价不超过 $8t-1$。分隔线上最多再按 $Z$ 次。

**达到上界。** 在一个小盘放入按从上到下、从左到右的位序编码的图案 $\mathtt{0x01BD}$，最低比特对应左上角。它到上述 16 个图案的最小距离为 7。在其余 $t-1$ 个小盘中，每一对放一张全零盘和一张全一盘。对于同一个零空间图案，这一对上的汉明距离之和恒等于 16。再把全部分隔格设为 1。按这个图案产生的灯态可解，而其每个解至少要按

$$Z+7+16(t-1)/2=Z+8t-1=17q^2-10q$$

次。证明给出了每个边长的最坏灯态构造，由真实的按键算子生成。[上下界和最坏灯态的构造](GridClicks.lean)

## 已有结论和公开证明核查

Boyles 已在同一修订稿证明，零空间维数四蕴涵 $n\equiv4\pmod{10}$，并在有限域稿中给出素数幂族的零空间维数。本包也从实际方盘形式化了这两个输入。Sloane 于 1986 年研究带重复列的二元线性码，并给出维数至多四时的归一化覆盖半径公式。他的结果为这类计数提供了另一条路线。这里补上的是具体方盘的精确代价、达到该代价的显式灯态和二者的 Lean 证明。[已知的边长同余](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L383-L420) · [素数幂的已知结论](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/finite_fields/finite_fields.tex#L1078-L1092) · [Sloane，A New Approach to the Covering Radius of Codes](https://neilsloane.com/doc/Me129.pdf) · [已知同余的形式化](FourIndex.lean)

截至 2026-11-27，核对了作者仓库四个公开分支、三份历史 PR、作者主页、OEIS 的两条相关条目，以及可索引的 arXiv、GitHub、AI 仓库和讨论。尤其对照了作者标明为 AI 生成的非默认分支文稿和新问题清单。里面已经证明多个零空间**维数**结论，在 MCP 部分则仍将上述二次式列为经验猜想，并记录 19 个精确数据点。GitHub 全局题号搜索中含同串十六进制数的无关文件较多，另用问题全名、公式、相关库的目录和 issue 检索。所查材料中未发现更早写出这个方盘代价公式之完整证明的公开文件。[修订稿与已知数据的范围](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L421-L457) · [作者的 AI 稿说明](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/README.md) · [作者的历史 PR](https://github.com/wmboyles/LightsOut-Math/pulls?q=is%3Apr) · [Boyles 2022 年预印本](https://arxiv.org/abs/2201.03452)

## 独立复验

独立 Python 程序从实际首行递推重建 16 个图案，遍历 $4\times4$ 方盘的全部 65,536 个按键向量，并在边长不超过 154 的 13 个四维样本上复核显式最坏灯态的全部 16 种解。作者公开表中的 19 个四维精确数值均与公式一致。Lean 对任意边长的结论来自上下界证明。[独立复核程序](check_clicks.py) · [原作者数据](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/code/serialization/min_clicks_answers.txt)

项目锁定 Lean 4.24.0 和 mathlib 提交。项目内的依赖模块由 Lake 先行构建。主定理为 GridClicks.every_nullity_four 与 GridClicks.five_powers，公理清单只含 propext、Classical.choice 和 Quot.sound。

```sh
lake exe cache get Mathlib.Algebra.CharP.Two Mathlib.Algebra.Field.ZMod Mathlib.Algebra.Polynomial.Degree.Lemmas Mathlib.Algebra.Polynomial.FieldDivision Mathlib.Algebra.Ring.GeomSum Mathlib.Data.Fintype.EquivFin Mathlib.Data.Nat.Bitwise Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Factorization.Basic Mathlib.Data.Nat.Size Mathlib.Data.ZMod.Basic Mathlib.FieldTheory.Finite.Basic Mathlib.FieldTheory.Finiteness Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.LinearAlgebra.Dimension.Constructions Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.Order.Preorder.Finite Mathlib.RingTheory.AdjoinRoot Mathlib.Tactic.IntervalCases Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring
lake build GridClicks
lake env lean -DwarningAsError=true GridClicks.lean
python3 check_clicks.py
```
