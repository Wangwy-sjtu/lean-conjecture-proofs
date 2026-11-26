# 单比特量子门的 Pauli 相关矩阵只要含零元，正性收益就等于零

Savadatti 和 Zhang 在单比特情形给出了九个 Pauli 相关系数全非零时的精确判据，并在命题 13 后明确说明有零系数的情形未被覆盖。本文补全这个边界情形。对于任意单比特酉信道，只要九个系数中至少一个为零，考虑 Choi 矩阵正半定性所得到的一阶认证收益便恒等于零。与原论文命题 13 合用，这给出了所有单比特量子门的判定。原论文的猜想 14 涉及两个比特的满支撑量子门，仍待解决。[原论文第 VII.5–VII.6 节](https://arxiv.org/html/2611.27724v1#S7.SS5)

## 物理量及与原文的联系

给定 $U\in SU(2)$，令 $|\Phi_U\rangle=(U\otimes I)(|00\rangle+|11\rangle)/\sqrt2$。整体相位在 Choi 投影中消去，任意单比特酉信道都可选取这样的代表。令 $i,j\in\{X,Y,Z\}$，定义实矩阵

$$
O_{ij}=\langle\Phi_U|\sigma_i\otimes\sigma_j|\Phi_U\rangle
=\tfrac12\operatorname{Tr}(\sigma_i U\sigma_j^{\mathsf T}U^\dagger).
$$

$O$ 正交。原论文的收益 $g(U)=s_{\rm wit}(U)-s_{\rm SDP}(U)$ 是移除与保留 Choi 正半定约束时的局部认证斜率之差。在 $O_{ij}\ne0$ 的位置，次梯度系数 $S_{ij}$ 必须是 $\operatorname{sgn}O_{ij}$，在零元处可以任取 $[-1,1]$ 中的数。选择所有单寄存器项为零后，迹保持的对偶条件自动满足。定义

$$
M=SO^{\mathsf T}+OS^{\mathsf T}-\left(\sum_{ij}|O_{ij}|\right)I_3.
$$

附录 A.7 使用 $e_i=(\sigma_i\otimes I)|\Phi_U\rangle$ 作为目标态正交补的正交基。该附录的 Pauli 三重乘积恒等式对每一项线性成立，因而对任意允许的 $S$ 都给出上述真实压缩矩阵。当 $M\preceq0$ 时，定理 3 式 (32) 的两个条件都满足，故 $g(U)=0$。支撑不足时，允许选择零位系数正是定理 3 式 (30)–(31) 的次梯度条件。这里直接构造这样的 $S$。[定理 3 及式 (29)–(32)](https://arxiv.org/html/2611.27724v1#S5) · [附录 A.7 的 Pauli 算符推导](https://arxiv.org/html/2611.27724v1#A1.SS7)

## 三阶实矩阵证明

先交换行和列，把一个零元移到右下角。正交性的最后一行和最后一列各给出一个平面单位向量。再用带符号的行列变换，可写成

$$
O_0=\begin{pmatrix}-qs&qr&p\\ps&-pr&q\\r&s&0\end{pmatrix},
\qquad p,q,r,s\ge0,\qquad p^2+q^2=r^2+s^2=1.
$$

形式化中从这两个单位向量推导其正交补都由一个向量张成，左上 $2\times2$ 块的剩余标量 $t$ 满足 $t^2=1$。行列变换时对 $O$、$S$ 同时重标，$M$ 只发生正交相似变换。这一论证还覆盖 $p,q,r,s$ 中有零的情形。

在上述坐标直接取

$$
S_0=\begin{pmatrix}-1&1&1\\1&-1&1\\1&1&0\end{pmatrix}.
$$

在每个位置都有 $|S_{ij}|\le1$ 且 $S_{ij}O_{ij}=|O_{ij}|$。令 $A=p+q$、$B=r+s$、$b=|r-s|$。$-M$ 的前三个对角元依次为 $B+(p-q)(B-1)$、$B-(p-q)(B-1)$、$A+(A-1)B$。三个非对角元的绝对值依次为 $A(B-1)$、$(1-q)b$、$(1-p)b$。每行的对角元减去其余元素绝对值之和依次为

$$
(1-q)(B-b)+q(2-B),\quad
(1-p)(B-b)+p(2-B),\quad
(A-1)(B+2)+(2-A)(1-b).
$$

单位圆条件给出 $1\le A,B\le2$、$0\le b\le\min(1,B)$。三项均非负，因此 $-M$ 正半定。Lean 对每个非对角项直接使用 $2kxy\le |k|(x^2+y^2)$ 完成同一论证。

## 形式化和交叉检查

| 文件或定理 | 实际覆盖 |
|---|---|
| `DeficientQubit.lean` 的 `deficient_certificate` | 对全部实三阶正交矩阵，只要任一位置为零，构造满足绝对值次梯度条件且压缩二次型半负定的实矩阵。 |
| `gate_certificate` | 从复 $2\times2$ 酉矩阵、单位行列式、实际 Pauli 迹中的一个零元出发，给出同一证书。程序展开 $X,Y,Z$、验证酉矩阵的 Cayley–Klein 形式和九个相关量的正交性。 |
| `check.py` | 使用有理数和全部主子式，检查 1,800 组正交矩阵的显式次梯度证书。按抽样中的零元个数分为 648 个一零元样本、864 个四零元样本、288 个六零元样本，计数含对称重复。脚本另将所有零位都填为零，并精确检查这些样本的压缩矩阵为负定。此较强的样本性质不用于全称证明。 |

量子门入口的形式化结论是 $M\preceq0$ 的次梯度证书。从证书到优化问题的 $g(U)=0$ 使用上述原论文定理 3 和压缩恒等式。原论文中的半定规划对偶理论未在此文件重新开发。该实对称压缩的复二次型是实部与虚部的两个实二次型之和，所以实向量检验也适用于全部复向量。

在 Lean 4.24.0、mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` 的项目目录中运行

```sh
lake env lean -DwarningAsError=true DeficientQubit.lean
python3 check.py
```

## 公开查重

2026 年 11 月 27 日（北京时间）以原作者、论文编号、`support-deficient`、`positivity gain`、`single-qubit`、`zero gain`、次梯度和 Pauli 相关矩阵的等价措辞检索原文、公开预印本和可检索的 AI 证明。原作者已经给出满支撑单比特判据、一个具有正收益的满支撑单比特实例，以及两比特 $T\otimes T$ 零收益的精确证明。[原文命题 13](https://arxiv.org/html/2611.27724v1#S7.SS5) · [原文附录 A.3](https://arxiv.org/html/2611.27724v1#A1.SS3)

- GitHub 的论文编号检索命中预印本元数据。面向本定理的代码、Issue 与 PR 检索未找到相同证明。作者在论文里给出的仓库地址通过公开访问返回 404，连接器的分支与 PR 查询也无法访问；其中是否存在其他版本无法核实。[论文编号的代码命中](https://github.com/jam-sudo/TrendBio/blob/0036bdca5bbcd6d9173bd155395fe884a65df9b2/data/physics/items/2026/11/arxiv_2611.27724.json) · [代码检索](https://github.com/search?q=%22support-deficient%22+%22positive+gain%22+qubit&type=code) · [Issue 检索](https://github.com/search?q=%222611.27724%22+Pauli&type=issues) · [作者所列仓库分支](https://api.github.com/repos/shreyasavadatti/positivity-pauli-certification/branches) · [作者所列仓库 PR](https://api.github.com/repos/shreyasavadatti/positivity-pauli-certification/pulls?state=all)
- 在 TrureTuring 当期公开结论索引中未查到作者、论文号或题名关键短语。另以作者和物理量查找 MathDB、Hexagon 和 EulerSolve 的公开记录，未找到相同结论。Hexagon 站内作者检索返回零条。公开检索不能排除未索引、不同术语或非公开的证明。[TrureTuring 索引](https://www.trureturing.org/conjectures.html?lang=en) · [MathDB 检索](https://www.google.com/search?q=site%3Amathdb.com+Savadatti+positivity+gain+qubit) · [Hexagon](https://hexagonmath.org/search?q=Savadatti) · [EulerSolve](https://www.eulersolve.org/papers/)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.LinearAlgebra.Matrix.Trace Mathlib.LinearAlgebra.Matrix.PosDef Mathlib.Data.Real.Basic Mathlib.LinearAlgebra.Matrix.Notation Mathlib.Algebra.BigOperators.Fin Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring Mathlib.Tactic.Positivity
lake env lean -DwarningAsError=true DeficientQubit.lean
```
