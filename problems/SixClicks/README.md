# 六维零空间方盘的最坏最少按键数

对标准方盘，每按一个格子就翻转该格和上下左右的邻格。记 $d(n)$ 为边长 $n$ 的方盘的零作用按键空间维数，记 $M(n)$ 为所有可解灯态中，最难者所需的最少按键次数。

**定理。** 如果 $d(n)=6$，则 $n=12q-1$，其中 $q$ 是正奇数，并且

$$M(n)=88q^2-24q+1.$$

这证明了 Boyles 修订稿经验公式表中的六维一行。原表给出六个精确数据点。例如边长 $11,35,83$ 对应 $65,721,4145$ 次。对任意 $k\ge0$，边长 $12\cdot3^k-1$ 自动满足六维条件。取 $k=3$ 得到边长 323 的方盘，它的最坏灯态恰需 63,505 次按键。[作者的猜想](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L432-L451) · [Lean 主定理](SixClicks.lean)

## 为什么只需研究一个 11 阶方盘

在 $11\times11$ 小盘上，任意一行的按键可由上一行和更上一行递推得到。要求最后一行的灯也恰好抵消后，允许的首行形成六维空间，共有 64 个零作用图案。将这 64 个图案按每个格子上的取值排列。121 个格子中有 9 个在所有图案中恒为零，其余 112 个格子各在恰好 32 个图案中取一。对后者，将在所有图案上取值相同的格子归入同一组。每组的格数都是偶数，实际出现的组大小只有 4 与 8。[六个基向量和有限核验证书](SixClicks.lean)

对任意按键图案，把同一零作用图案加进去会得到同一灯态的另一组解。取遍 64 种选择，每个活跃格平均贡献半次，固定的 9 格最多贡献 9 次，所以最少按键数至多为 $9+112/2=65$。这个均值上界可以逐个图案同时达到。先点亮按键向量的全部固定格，再在每个等值组内任意选恰好一半格子按下。加入任何零作用图案只会同时翻转整组或保持整组，所以每个组的按键数都保持一半。把这个向量作用到全灭盘得到的灯态，每一份解都恰有 65 个按键。[显式见证与独立复核](check_six.py)

将同一个小盘图案在水平、垂直方向镜像铺成 $q^2$ 块，两块间留一行或一列零。它仍是大盘的零作用图案。当大盘也有六维零空间时，64 个不同延拓已经给出大盘的全部零作用图案。最坏灯态的按键向量在全部分隔格置一，并在每个小盘复制刚才的见证。所有 64 份解都恰需

$$((12q-1)^2-121q^2)+65q^2=88q^2-24q+1$$

次。相反，任意灯态的每个解可同时加上这 64 个延拓，分隔格最多各按一次，各小盘对这 64 个选择的平均按键数至多为 65，所以至少有一份解不超过这个总数。[可复用的平均上界与见证定理](SeedCosts.lean) · [真实翻转的镜像延拓](ReflectionTiles.lean)

## 已有结论、查重和复验

原作者已经证明六维方盘必有 $n\equiv11\pmod{24}$，也给出了 $12\cdot3^k-1$ 的维数规律。这里为两者附了 Lean 证明。作者的公开 Lean 文件 GridClicks.lean 已完整处理维数二和 5 阶小盘，MirroredPath.lean 已处理任意路径上的镜像延拓；该包对六维方盘增加精确的按键上下界和最坏灯态。Sloane 的重复列码理论涵盖相同列偶数次出现时的配对原理。2026-11-27 核对了作者仓库的四个公开分支、三个历史 PR、其 AI 稿目录与对应 Lean 源码，并按公式和题名在网上、arXiv、GitHub 与公开 AI 证明目录检索。在查到的来源中，六维公式仍以经验猜想出现。[作者的尺寸定理](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L383-L420) · [已有的二维 Lean 定理](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/lean/LightsOut/GridClicks.lean#L411-L466) · [已有的一般路径延拓](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/lean/LightsOut/MirroredPath.lean#L262-L376) · [作者的 AI 稿目录](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/README.md) · [Sloane 1986](https://neilsloane.com/doc/Me129.pdf)

Python 独立地从物理首行递推构造小盘基、等值组、见证和大盘的全部 64 种解，并与作者六个已知点逐项核对。Lean 从五格翻转及其零空间证明任意边长的结论，三个主定理只依赖 propext、Classical.choice、Quot.sound。[作者的精确数值](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/code/serialization/min_clicks_answers.txt) · [边长分类与三幂族](SixIndex.lean)

```sh
lake exe cache get Mathlib.Algebra.CharP.Two Mathlib.Algebra.Field.ZMod Mathlib.Algebra.Polynomial.Degree.Lemmas Mathlib.Algebra.Polynomial.FieldDivision Mathlib.Algebra.Ring.GeomSum Mathlib.Data.Fintype.EquivFin Mathlib.Data.Nat.Bitwise Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Factorization.Basic Mathlib.Data.Nat.Size Mathlib.Data.ZMod.Basic Mathlib.FieldTheory.Finite.Basic Mathlib.FieldTheory.Finiteness Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.LinearAlgebra.Dimension.Constructions Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.Order.Preorder.Finite Mathlib.RingTheory.AdjoinRoot Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring
lake build SixClicks
lake env lean -DwarningAsError=true SixClicks.lean
python3 check_six.py
```
