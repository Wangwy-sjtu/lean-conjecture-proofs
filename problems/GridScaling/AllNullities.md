# 零空间维数有界时，整个方盘序列最终服从一个准多项式

取任意有限上界 $d$。对所有零空间维数不超过 $d$ 的标准方盘，可以用同一张有限表描述最坏最少按键数。具体地，存在正周期 $P$、起点 $N_0$ 以及每个余数 $r$ 对应的两个有理数 $A_r,C_r$。凡边长 $n\ge N_0$ 且零空间维数不超过 $d$，取 $r=(n+1)\bmod P$，则

$$M(n)=n^2-A_r(n+1)^2-C_r.$$

这就是在指定边长集合上的最终二次准多项式，每个余数类使用一个普通二次式。固定一个零空间维数时，直接取该维数为 $d$ 即可。小盘种类、铺盘倍数和它们的奇偶性均由同一余数类处理。定理不要求预先指定一块小盘，也不假设同一余数类的所有方盘都满足维数界。给定的周期足以使结论成立，证明未把它优化到最小。[作者的高维最坏按键问题](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L453-L457) · [Lean 主定理](NullityQuasipolynomial.lean)

## 如何用一个模数为所有方盘选择基准盘

写 $N=n+1$，在二元多项式环中定义 $F_0=0,F_1=1,F_{j+2}(x)=xF_{j+1}(x)+F_j(x)$。方盘的零空间维数等于下列公因式的次数

$$g_N=\gcd(F_N(x),F_N(x+1)).$$

这是已有的格点零空间公式，包内附从按键算子出发的证明。[方盘与多项式商空间的对应](GridGcd.lean)

对次数不超过 $d$ 的每个二元多项式 $p$，令 $a_p$ 是它同时整除 $F_a(x)$ 与 $F_a(x+1)$ 的最小正指标。如果没有这样的正指标，置 $a_p=1$。共有有限多个 $p$。取 $L$ 为所有这些 $a_p$ 的乘积。一个这样的共同指标的任意倍数仍是共同指标。两个共同指标的非负差也是共同指标，这由特征二的恒等式给出

$$F_{j+k}F_{k+1}+F_{j+k+1}F_k=F_j.$$

对于存在正共同指标的 $p$，反复作差可见 $a_p$ 整除它的每个共同指标。现在取 $p=g_N$，其次数满足上界。于是 $a_p$ 整除 $a=\gcd(N,L)$，从而 $g_N\mid g_a$。又因为 $a\mid N$，有 $g_a\mid g_N$。两块方盘的零空间维数相同。这样，任何符合条件的大盘都由基准盘 $a-1$ 表示；同一个 $L$ 适用于所有这些边长。[有限模数与双向整除的证明](FiniteSeeds.lean)

## 为什么余数足以确定二次式

取 $P=2L$。$N\bmod 2L$ 同时确定 $a=\gcd(N,L)$ 和倍数 $Q=N/a$ 的奇偶性。基准盘上有 $H$ 个活跃格。前一结果给出 $2M(n)=2n^2-HQ^2-e$，其中偶数倍恒有 $e=0$，奇数倍从某一阈值起有固定的 $e$。代入 $Q=(n+1)/a$，得到 $A_r=H/(2a^2)$ 与 $C_r=e/2$。余数类只有有限个，所以所有阈值有共同上界。[固定基准盘的上下界](GridScaling.lean) · [合并全部余数类](NullityQuasipolynomial.lean)

## 已有工作与独立复验

Boyles 的公开仓库中，一份标注为 AI 生成的文稿已证明每个可达的正零空间维数都有有界的见证方盘，并能在有限范围判定维数是否可达。该文稿的压缩步骤还保持指标整除关系。原作者也已公开镜像延拓。Sloane 1986 年分析了二元码重复列的归一化覆盖半径和单调性。本次结合这些背景给出按同一模数分类的**最坏按键数**准多项式，并独立形式化分类所需的公因式降阶。2026-11-27 核对了作者的非默认分支、AI 稿、现有 MCP Lean 定理和问题目录，以及可索引的 arXiv、网页和 GitHub 材料。Brouwer 的矩形表给出固定一边时的维数周期，研究的是另一统计量。[已有 AI 有限见证定理](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/finite_witness_bounds/finite_witness_bounds.tex) · [已公开的二维方盘按键定理](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/lean/LightsOut/GridClicks.lean#L411-L466) · [Sloane 原文](https://neilsloane.com/doc/Me129.pdf) · [Brouwer 矩形表](https://aeb.win.tue.nl/ca/madness/madrect2.html)

独立 Python 程序对索引 1 至 720 和维数上界 0 至 6 计算二元多项式余数。它核对了 3,241 个模数降阶实例，其中 2,949 次确实缩小了基准盘。边长小于 200 的 893 项又用物理方盘的首行消元和相应已知精确按键式交叉复核。Lean 的全称命题对任意有限 $d$ 成立，仅依赖三个标准公理。[独立复核程序](check_global.py)

```sh
lake build NullityQuasipolynomial
lake env lean -DwarningAsError=true NullityQuasipolynomial.lean
python3 check_global.py
```
