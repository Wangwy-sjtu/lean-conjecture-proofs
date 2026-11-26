# 固定零空间方盘的最坏按键次数为何会出现二次式

零空间维数恰为八的方盘已经需要区分余数类。两个无穷族的二次项系数不同，所以单个普通多项式无法同时描述它们。[八维反证和具体增长率](EightFamilies.md)

对所有零空间维数不超过任意指定上界的方盘，还有一条统一的准多项式定理。它按边长的余数类取二次式，一次覆盖所有基准盘。[全体有界维数方盘的定理和证明](AllNullities.md)

设 $M(n)$ 为标准 $n\times n$ Lights Out 方盘所有可解初始灯态中，最难者所需的最少按键次数。固定边长 $m$ 的小盘。设 $H$ 为小盘中能被至少一种零作用按键图案覆盖的格数。放大倍数为正整数 $Q$，大盘边长为 $n=(m+1)Q-1$。以下结论适用于大盘与小盘零空间维数相同的每个 $Q$。

**定理。** 偶数 $Q$ 满足 $2M(n)=2n^2-HQ^2$。对每个小盘还存在两个只依赖于 $m$ 的非负整数 $D,K$，使所有 $Q\ge K$ 的奇数倍满足

$$2M(n)=2n^2-HQ^2-D.$$

因此，在维数保持不变的放大倍数上，最坏按键数最终按奇偶分别服从二次多项式。此结论回答了 Boyles 修订稿中“固定维数族按倍数变化”问题的一个结构性部分。假设指定了基准盘和容许的倍数。是否从第一个奇数倍就适用，以及两个不同基准盘在同一维数下是否给出同一个多项式，均需另行判定。[作者的问题及经验公式](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L432-L457) · [Lean 主定理](GridScaling.lean)

## 从按键规则到覆盖半径

将小盘的零作用图案镜像铺成 $Q\times Q$ 块，相邻块之间留一行或一列零。在分隔线上，两侧影响成对消去，边界也是零，故延拓仍为零作用图案。首块保留整个原图案，所以延拓是单射。两个零空间的维数相等时，延拓给出全部大盘零作用图案。这一步在 Lean 中直接使用翻转自身与正交邻格的算子。[普遍镜像延拓](ReflectionTiles.lean) · [方盘坐标双射](ReflectionLayout.lean)

记 $r=Q^2$。恰有 $n^2-rH$ 个大盘格在所有零作用图案中恒为零。在构造最坏初始灯态时，可以把生成它的按键向量在这些位置全部置一。剩余位置由同一个小盘零作用图案重复 $r$ 次。设 $R_r$ 为任意二进制输入到这些重复图案的最近距离的最大值，则

$$M(n)=n^2-rH+R_r.$$

等号的两个方向均在真实灯态上成立。两个按键向量产生相同灯态，恰当且仅当其差是零作用图案。[精确覆盖半径公式](GridScaling.lean) · [物理按键算子](PressCost.lean)

对任一个活跃格，选定在那里取一的零作用图案。加上该图案将整个零空间中的取零和取一者配对。因此每个输入到全部候选的平均距离是 $rH/2$，从而 $2R_r\le rH$。再取一个达到 $R_r$ 的输入，在末尾添一块全零、一块全一。无论选哪个零作用图案，新添两块的距离和恒为 $H$，故 $R_{r+2}\ge R_r+H$。非负整数 $D_r=rH-2R_r$ 沿每个奇偶子列单调不增。偶数列从 $D_0=0$ 开始，奇数列最终达到其最小值。这给出上述结论，也解释了偶数倍的等式为何从一开始就成立。[覆盖半径的配对与稳定性](RepeatedCover.lean)

## 先例与复核

镜像铺盘归于 Boyles。Sloane 1986 年对一般重复列二元线性码建立了归一化覆盖半径理论，其定理 2 给出增加两列的单调性。上述编码论稳定机制已有这一先例。本包将其应用到方盘，确定活跃格数如何给出二次项，并从实际五格按键规则机检公式。2026-11-27 核对了作者四个公开分支、三个历史 PR、AI 稿目录、arXiv 论文和可检索的 GitHub 讨论。修订稿仍将高维最坏按键的多项式性列为问题。该检索的结论限于所见公开资料。[Sloane 原文](https://neilsloane.com/doc/Me129.pdf) · [作者已给出的镜像铺盘](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/finite_fields/finite_fields.tex#L365-L395) · [作者的 AI 稿索引](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/README.md) · [2022 年原论文](https://arxiv.org/abs/2201.03452)

独立 Python 程序从首行消元重建零空间，在 102 个放大算例上逐一验证零作用图案、每个格型的重复数和固定格数，其中 46 个满足零空间维数相等。主证明适用于任意边长。两个主定理的公理清单均只含 propext、Classical.choice 与 Quot.sound。[独立复核脚本](check_scaling.py)

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Group.Finset.Piecewise Mathlib.Algebra.CharP.Two Mathlib.Algebra.Field.ZMod Mathlib.Algebra.Polynomial.Degree.Lemmas Mathlib.Algebra.Polynomial.FieldDivision Mathlib.Algebra.Polynomial.Roots Mathlib.Algebra.Ring.GeomSum Mathlib.Data.Finset.Max Mathlib.Data.Fintype.EquivFin Mathlib.Data.Nat.Bitwise Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Factorization.Basic Mathlib.Data.Nat.Size Mathlib.Data.Real.Basic Mathlib.Data.ZMod.Basic Mathlib.FieldTheory.Finite.Basic Mathlib.FieldTheory.Finiteness Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.LinearAlgebra.Dimension.Constructions Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.Order.Preorder.Finite Mathlib.RingTheory.AdjoinRoot Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring
lake build GridScaling
lake env lean -DwarningAsError=true GridScaling.lean
python3 check_scaling.py
```
