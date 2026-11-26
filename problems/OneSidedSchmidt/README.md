# 固定一侧 Schmidt 基时，另一侧的最佳局部酉可取恒等

Busoni、Gargalionis、Wallace、White 在 Hypothesis 1 中问，两个素数维系统上的非局域魔性是否总能由计算基 Schmidt 对齐态达到。其目标是对两侧局部酉同时优化二阶稳定子 Rényi 熵。这里固定其中一侧。**若 B 端 Schmidt 基已放在计算基中，并固定其标号，则无论 A 端取怎样的局部酉，熵都无法低于双侧对齐态。** 此结论覆盖每个局部维数 $d\ge2$ 以及每个整数 Rényi 阶 $m\ge2$，包括复合维数。原文的两侧共同优化问题仍然开放。[Busoni 等，Hypothesis 1、式（34）至（42）](https://arxiv.org/html/2603.09155v2#S3) · [Physical Review A 114, 042414](https://journals.aps.org/pra/abstract/10.1103/jh55-rmc6)

## 精确的集合和结论

取两个 $d$ 维系统，标签群 $G=\mathbb Z/d\mathbb Z$，令 $z_j\ge0$、$\sum_j z_j^2=1$。标号 $j\mapsto z_j$ 任意固定，无需将振幅排序。定义

$$
 |\psi_z\rangle=\sum_{j\in G}z_j |j\rangle_A|j\rangle_B,
 \qquad |\psi_{z,U}\rangle=(U\otimes I)|\psi_z\rangle,
 \quad U\in U(d).
$$

每个 $d$ 能级系统采用 $d^2$ 个循环 Weyl 算符 $W_{a,b}|i\rangle=\omega^{ib}|i+a\rangle$，其中 $\omega=e^{2\pi\mathrm i/d}$，所有下标模 $d$。对于 $d=2^r$，这个算符族的定义仍是单个 $d$ 能级系统的循环 Weyl 算符。双系统的 Hilbert 空间维数为 $d^2$。未归一化矩与熵为

$$
 Q_m(\psi)=\sum_{a,b,h,t\in G}\left|\langle\psi|W_{a,b}\otimes W_{h,t}|\psi\rangle\right|^{2m},
 \qquad M_m(\psi)=-\frac{\ln(Q_m(\psi)/d^2)}{m-1}.
$$

**定理。** 对每个整数 $m\ge2$、任意上述 $z$ 和任意 $U\in U(d)$，有

$$
 M_m(\psi_z)\le M_m(\psi_{z,U}).
$$

恒等酉属于允许集合，所以左端确为单侧轨道的最小值。量词允许从任意一份标号的谱分别出发。B 端标号重排关系到不同轨道之间的比较；对单侧定理的具体应用，可以先选择所需 B 端标号。有了单侧最优性，若一个两侧变换能严格改进某个固定对齐态，它无法通过只变换 A 端来实现；交换两边可得同样的 B 端结论。

## 证明

写 $u_j=U|j\rangle$。固定 B 端位移 $h$，记 $w_j=z_j z_{j+h}$。对 A 端的 Weyl 算符 $P$ 定义 $c_P(j)=\langle u_{j+h}|P|u_j\rangle$。直接展开两体态的指标得到

$$
 \langle W_P\otimes W_{h,t}\rangle=\sum_{j\in G} w_j c_P(j)\omega^{jt}.
$$

对任意两个单位向量 $u,v$，每个 Weyl 矩阵元的模不超过 1，且 $\sum_P|\langle u|P|v\rangle|^2=d$。第二条可用有限 Fourier 正交关系逐个相位求和，再对平移求和得到。Lean 在循环 Weyl 的显式定义上证明了这两个性质。

展开 Fourier 和的 $2m$ 次模方。对 $t$ 求和保留两组 $m$ 元组 $(x_i)$、$(y_i)$，它们满足 $\sum_i x_i=\sum_i y_i$。每项的实非负权重为 $\prod_i w_{x_i} w_{y_i}$。对剩余的复系数取模并对 $P$ 求和，得到

$$
 \sum_P\left|\prod_i c_P(x_i)\overline{c_P(y_i)}\right|
 \le \sum_P |c_P(x_1)c_P(y_1)|\le d.
$$

第一步用其余 $2m-2$ 个因子的模均不超过 1，第二步用 Cauchy–Schwarz 和两个 Weyl 平方和。因而固定 $h$ 的总矩至多为 $d\sum_t|\sum_j w_j\omega^{jt}|^{2m}$。在 $u_j=|j\rangle$ 时，只有 A 端位移同为 $h$ 的算符有贡献，其 $d$ 个相位恰对 $t$ 作平移，所以这个上界被对齐态达到。对 $h$ 求和后，$Q_m(\psi_{z,U})\le Q_m(\psi_z)$。恒等 Weyl 算符给出模等于 1 的项，故两边矩均为正；取自然对数并乘负数给出熵的不等式。

## 哪些步骤进入了 Lean

| Lean 声明 | 实际核验范围 |
| --- | --- |
| `fourier`、`fourier_square`、`moment_tuple` | 在 `ZMod d` 上使用 mathlib 的标准复加性特征，证明 Fourier 正交后的元组展开，适用于每个正整数矩阶。 |
| `even_fourier_majorant` | 对每项模不大于 1、每列平方和不大于 $d$ 的复数组，证明上面的整阶 Fourier 矩界。 |
| `weyl`、`weyl_tight`、`correlation_state` | 由单侧 Weyl 显式公式证明平方和等于 $d$，并由双侧张量 Weyl 的实际期望式得到固定 $h$ 的 Fourier 表达。 |
| `coordinate_attains`、`unilateral_optimality` | 证明计算基取得上界。定理中的移动列甚至可以是任意一组单位向量，证明只需要各列归一化。 |
| `one_sided_unitary_renyi` | 直接量化 mathlib 的 `Matrix.unitaryGroup (ZMod d) ℂ`，从 $U^\dagger U=I$ 验证列范数，再完成归一化、矩为正及自然对数方向。`k : ℕ` 对应熵阶 $m=k+2$。 |

`OneSidedSchmidt.lean` 使用 Lean 4.24.0 和 mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。文件末尾三条 `#print axioms` 均只列出标准基础 `propext`、`Classical.choice`、`Quot.sound`。进入独立包目录后运行以下命令。

```sh
lake exe cache get Mathlib.Analysis.Fourier.ZMod Mathlib.LinearAlgebra.UnitaryGroup Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true OneSidedSchmidt.lean
python3 check.py
```

独立脚本在 $d=2,3,4,5,6$、$m=2,3,4$ 上直接遍历 $d^4$ 个复相关量。它用五组整数振幅、两个有理正交平面旋转的乘积，以及单侧 Weyl 平移构造测试态，在各维数的分圆多项式商环上做精确整数运算。15 个旋转比较都严格小于对齐态的矩，15 个 Weyl 平移保留相等的矩。在 $d=5,m=2$ 的旋转矩与对齐矩之比约为 $0.231792$。这些样例用于检查标号、归一化和不等式方向，全称定理由 Lean 证明。

## 公开文献和 AI 证明查重

查重截至 2026 年 11 月 27 日（北京时间）。最接近的结果与本题使用不同的允许酉集合或指标。

- Busoni 等的原文提出 $m=2$ 的两侧局部酉问题。其式（35）量化 $U_A\otimes U_B$，式（37）至（42）导出对齐态的矩。他们为两个三能级、五能级系统给出数值支持，并在两个四能级系统上报告同时优化的反例。本定理证明的是固定 B 端计算基及其标签后的整条单侧酉轨道。[原文和附录的数值检验](https://arxiv.org/html/2603.09155v2#A1)
- Liu、Cui 式（4）及附录 B 把多量子比特的两侧优化化为 $U\otimes U^*$ 的同步转动，并证明排序参考态在任意局部酉方向是局部极小。本题量化 $U\otimes I$ 的全部酉、单个循环 $d$ 能级系统，以及该轨道的全局极小值。Sierant 在多量子比特、二阶 Rényi 熵下证明了特定谱的两侧结果。两组成果与本题交叉处的特例应归于已有文献。[Liu、Cui 式（4）至（5）](https://arxiv.org/html/2609.01993v2#S2) · [Sierant 原文](https://arxiv.org/abs/2609.13106)
- 公开的 Asakitan 证明项目和 EDGE-Public 中文稿涉及二元标签系统上的单项局部酉、即基矢置换与相位。核查了具体证明及作用群。本文移动一侧的酉可以任意混合计算基。经典的整偶次 Fourier majorant 性质也是相关的证明方法；这里再使用 Weyl 平方和以取得并达到因子 $d$。[Asakitan 证明原文](https://github.com/Asakitan/monomial-stabilizer-renyi-rearrangement/blob/proof-v1.0.0/PROOF.md) · [EDGE-Public 中文原稿](https://github.com/LUOLINGc325/EDGE-Public/blob/a8874a1f014734e48051e445d20ca7be741b552b/papers/haar-schmidt-magic/paper.zh.md) · [Green、Ruzsa 关于 Hardy–Littlewood majorant 问题](https://arxiv.org/abs/math/0303244)
- GitHub 查过 `one-sided`、`unilateral`、`Weyl frame`、`one-sided optimality` 配合 `Schmidt`、`magic`、`stabilizer Rényi` 的代码与 Issue，实际命中包括上述单项酉稿件、文献索引及无关庞大词表。Hexagon 站内 `nonlocal magic` 返回 0 篇；另检索了 MathDB、EulerSolve 的公开索引和量子开放题 E27。所查来源中未找到全循环维数、全整数阶、单侧任意酉定理的公开证明。未索引、订阅内容和私人手稿不在这项核查范围内。[MathDB](https://mathdb.com/) · [E27 相关公开问题](https://open-quantum-problems.vercel.app/p/E27)
