# 两比特满支撑 Pauli 符号的平均谱偏度严格低于 Clifford 基准

Savadatti 与 Zhang 在式 (57) 后提出，两比特满支撑 Pauli 符号图的平均谱偏度是否满足 $\bar\kappa\le\kappa_{\rm stab}=1/\sqrt3$。这里给出对全部 $15\times15$ 个正负号都成立的严格不等式

$$
|\bar\kappa|\le \frac{58}{45\sqrt5}=0.576408634\ldots
<\frac1{\sqrt3}=0.577350269\ldots .
$$

它自动覆盖来自满支撑两比特门的全部符号图。原论文定义的 $\bar\kappa$ 是三阶矩期望除以二阶矩期望的 $3/2$ 次幂。另一个关于正性收益的猜想 14 还需要控制压缩的第二大特征值，仍待解决。[原文第 VII.3 节，式 (53)–(57)](https://arxiv.org/html/2611.27724v1#S7.SS3) · [猜想 14](https://arxiv.org/html/2611.27724v1#S7.SS6)

## 从物理量得到有限问题

两比特有 15 个非恒等 Hermitian Pauli 算符。任选两个有序的、可交换且不同的算符 $P,Q$。把其乘积写作 $PQ=\omega(P,Q)T$，其中 $T$ 是以标准正相位表示的 Pauli 算符，$\omega(P,Q)\in\{-1,+1\}$。共有 15 条无序直线 $\{P,Q,T\}$，每条有 6 种排列，共 90 个有序检验。用 $e=(P_1,P_2,P_3)$ 表示其中之一，写 $\omega_e=\omega(P_1,P_2)$。

对任意满支撑符号矩阵 $S\in\{-1,1\}^{15\times15}$，论文定理 9 式 (52) 的三角统计量为

$$
\Delta_c(S)=\sum_{e,f}\omega_e\omega_f
S_{P_1Q_1}S_{P_2Q_2}S_{P_3Q_3},
\qquad f=(Q_1,Q_2,Q_3).
$$

论文引理 8 式 (49) 给出 $\mathbb E\operatorname{Tr}R^2=180$，定理 9 式 (51) 给出 $\mathbb E\operatorname{Tr}R^3=(4/15)\Delta_c$。代入式 (57) 得 $\bar\kappa=(4/15)\Delta_c/(180\sqrt{180})$。这里固定局部维数 $d=4$，期望遍历第一个寄存器上的 Haar 单位向量。[引理 8 和定理 9](https://arxiv.org/html/2611.27724v1#S7.SS2)

## 为什么 90 项三线性和有统一上界

固定输入检验 $e$。此时矩阵 $S$ 的三行给出三组可以完全独立的赋号 $x,y,z$。对输出检验 $f=(P,Q,T)$，所需估计是一项常数符号 $\varepsilon$ 乘以下式

$$
L(x,y,z)=\sum_{(P,Q,T)}\omega(P,Q)\,x(P)y(Q)z(T).
$$

1. 在两比特 Pauli 几何的十个 Peres–Mermin 方阵里，每个方阵含九个点、六条行列直线。六条线的乘积符号相乘为 $-1$，每条 Pauli 直线出现在四个方阵里。这是已知的有限几何事实。[Li、Gupta、Ganesh，引理 7–9](https://arxiv.org/html/2610.26465v1#S4)
2. 在一个方阵中，把格子 $(i,j)$ 分给角色 $(i+j)\bmod3$。每个角色固定使用 $x,y,z$ 中的一组赋号。每行、每列恰出现三个不同角色，所以每条行列线都给出一个有序检验。将六个检验的期望符号相乘，九个被赋予的值都出现两次，统一符号 $\varepsilon$ 出现六次，剩下的因子为 $-1$。这六个检验里至少有一项为负。
3. 枚举三个角色的六种置换。在每条给定直线上，它们恰好产生全部六种有序检验。十个方阵因此产生 60 组约束，每个有序检验恰被计四次。若 $N$ 为 90 个检验中的负项总数，则 $4N\ge60$。
4. 所有 90 项相乘时，每个角色在每个点的符号出现六次，每条线的乘积符号也出现六次，统一符号出现 90 次。因此 $N$ 是偶数，$N\ge16$。正负项之和为 $90-2N\le58$。对 $\varepsilon=\pm1$ 应用同一结论便得到 $|L|\le58$。

对 90 个输入检验求和，得 $|\Delta_c|\le90\cdot58=5220$。最后的严格比较可直接平方，得到 $3\cdot58^2=10092<10125=45^2\cdot5$。

## 形式化及独立复算

| 定理或脚本 | 实际核验范围 |
|---|---|
| `pauli_geometry` | 用 $I,X,Y,Z$ 乘法相位表验证 90 个有序对各出现一次，算符乘积的标号和符号都与列举一致。 |
| `at_least_sixteen` | 对三组任意独立赋号及统一符号，正式证明每组方阵约束的奇性、总计的偶性及 16 的整数下界。 |
| `triangle_bound`、`commutingTriangles_eq` | 验证 5,220 的普适上界，并显式构造 90 项编号与原文“所有不同、可交换的非恒等 Pauli 有序对”之间的双射，再重写双重求和。 |
| `skew_bound` | 从原文两个已给定的矩公式所确定的函数，对全部 $2^{225}$ 种符号选择证明实数偏度界及其相对 Clifford 基准的严格差距。 |
| `check.py` | 用高斯整数 $4\times4$ 矩阵直接重建 Pauli 乘法与十个方阵，比对 Lean 的四个有限数据表，并独立穷举三线性和的精确范数。 |

Lean 的物理入口把引理 8 与定理 9 的已发表预印本矩公式代入式 (57)。Haar 积分公式在此作为文献输入。Lean 源码独立证明此后全部组合与实数不等式，未引入开放结论作为前提。数据表用整数按位存储，脚本从矩阵重新构造并逐表比对。五项公理审计只列出 Lean/mathlib 的标准公理。

在 Lean 4.24.0、mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` 的 Lake 项目目录里，把两个文件置于同一目录后运行

```sh
lake env lean -DwarningAsError=true PauliSkew.lean
python3 check.py
```

脚本还精确得到 $\max_{x,y,z}|L(x,y,z)|=54$。它用五个已显示的 Clifford 共轭生成元把第一组 $2^{15}$ 种赋号分为 12 个轨道，在每个轨道枚举第二组的全部 $2^{15}$ 种取值，再对第三组逐项取最优符号。三组全部为 $+1$ 时达到 54。这一独立穷举把偏度上界进一步改进到 $6/(5\sqrt5)\approx0.536656315$。Lean 文件证明的常数为 $58/(45\sqrt5)$。这两个数是本证明对谱偏度给出的上界，物理符号图能取得的精确最大值仍未知。

## 相近定理和公开查重

2026 年 11 月 27 日（北京时间）查了作者、原论文号、`spectral skew`、`commuting triangles`、`three-player`、`doily`、`trilinear` 及等价的三个赋号问题。

- Li、Gupta、Ganesh 的引理 8 已给出十个方阵和四重覆盖，引理 9 从方阵奇偶矛盾推出单一共同赋号至少违反三条无序直线。本证书使用这个已知覆盖。三组独立的赋号在同一个点可以不同，本文用拉丁方逐个保持格子的角色并利用 90 个有序检验的全局偶性。该近邻项目公开的五个分支和四个 PR 都已查阅标题、说明或 README，未查到本文的三赋号偏度结论。[原论文](https://arxiv.org/abs/2610.26465) · [代码与分支](https://github.com/BrianLi009/four-qubit-hyperbolic-quadric/branches) · [公开 PR](https://github.com/BrianLi009/four-qubit-hyperbolic-quadric/pulls?q=is%3Apr)
- Kelleher、Roomy、Holweck 研究了以相同两比特几何构造的双人量子伪心灵感应游戏，双方接受的提问及胜利条件和这里的三独立赋号统计量不同。[Doily 游戏原文](https://arxiv.org/abs/2310.07441)
- GitHub 全站的精确术语代码检索和论文号加偏度的 Issues、PR 检索没有返回相同证明。Savadatti–Zhang 原文所列的仓库在公开网页返回 404，分支接口与 PR 搜索也无法访问。以作者、论文号及完整术语查了当前可访问的 TrureTuring、MathDB、EulerSolve 记录。Hexagon 对 `commuting triangle spectral skew` 的精确站内检索为零条。检索覆盖公开可访问资料，仍可能遗漏术语不同、未索引或未公开的证明。[GitHub 代码](https://github.com/search?q=%22commuting+triangles%22+%22spectral+skew%22&type=code) · [Issues](https://github.com/search?q=%222611.27724%22+%22skew%22&type=issues) · [原作者分支接口](https://api.github.com/repos/shreyasavadatti/positivity-pauli-certification/branches) · [原作者 PR 接口](https://api.github.com/repos/shreyasavadatti/positivity-pauli-certification/pulls?state=all) · [TrureTuring](https://www.trureturing.org/conjectures.html?lang=en) · [MathDB 检索](https://www.google.com/search?q=site%3Amathdb.com+Savadatti+spectral+skew+Pauli) · [Hexagon](https://hexagonmath.org/search?q=commuting+triangle+spectral+skew) · [EulerSolve](https://www.eulersolve.org/papers/)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.ZMod.Basic Mathlib.Data.Real.Sqrt Mathlib.Data.Fin.VecNotation Mathlib.Algebra.BigOperators.Fin Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.Positivity
lake env lean -DwarningAsError=true PauliSkew.lean
```
