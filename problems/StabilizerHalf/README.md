# 两比特纯态的最大半阶稳定子 Rényi 熵

对任意两比特纯态，稳定子范数 $D$ 与半阶稳定子 Rényi 熵满足

$$\max D=1+\frac{\sqrt3}{2},\qquad
  \max M_{1/2}=2\ln\!\left(1+\frac{\sqrt3}{2}\right).$$

Liu、Low、Yin 以数值证据提出某个态在 $\alpha<1.64\ldots$ 时达到最大，特别点名 $\alpha=1/2$。Lean 验证了这个指定阶的全局上界和作者给出的态达到上界。原猜测中其余 $0<\alpha<1.64\ldots$ 的阶数仍待研究。线性代数和算术证明对所有两比特纯态成立，没有外部物理定理假设。[arXiv 原文脚注 2](https://arxiv.org/pdf/2502.17550#page=4) · [期刊版脚注 4](https://doi.org/10.1088/2058-9565/ae3028)

Liabøtrø 于 2017 年已对等价的两比特带符号 Pauli 算符界穷尽数值检查，并给出了因式分解的取等构造。TrureTuring 后来在三比特证明了一般维数猜想存在反例，并公开报告同一个两比特数值。这里补上两比特全局界的精确证明，给出达到极端特征值的符号矩阵数量，并直接验证 Liu 等所写的矢量。[Liabøtrø，式 (75)–(78) 和表 IV](https://arxiv.org/pdf/1607.02667#page=10) · [TrureTuring 的原始结果及其后续数值记录](https://www.trureturing.org/research/liabotro-2017-signed-pauli-sum-norm/)

## 从纯态到四阶厄米矩阵

按 $I,X,Y,Z$ 排列单比特 Pauli 矩阵，按张量积字典序取去掉 $II$ 的 15 个两比特 Pauli 串。记 $r_P=\langle w|P|w\rangle/\langle w|w\rangle$，允许任意非零复向量 $w$。按原作者的自然对数约定，

$$D(w)=\frac{1+\sum_{P\ne II}|r_P|}{4},\qquad M_{1/2}(w)=2\ln D(w).$$

对每个 $P$ 选 $s_P\in\{-1,1\}$ 与 $r_P$ 同号。绝对值之和成为 $H_s=\sum_{P\ne II}s_P P$ 的期望值。令 $L=3+2\sqrt3$。只要证明任何符号选择都没有超过 $L$ 的特征值，就得到了对所有纯态的上界。

将 15 个符号写为两个三维向量 $u,v$ 及一个 $3\times3$ 矩阵 $C$。它们依次对应 $\sigma_i\otimes I$、$I\otimes\sigma_j$ 和 $\sigma_i\otimes\sigma_j$。设 $d_{ij}=u_i C_{ij}v_j$，$h=\prod_i u_i\prod_j v_j$，并记 $K=\operatorname{cof}(d)$ 为余因子矩阵。直接展开四阶行列式，得到

$$\det(tI-H_s)=t^4-30t^2+a t+b,$$

$$a=-8\left(\sum_{ij}d_{ij}-h\det d\right),$$

$$b=225-4\!\left(
\sum_i\left(\sum_j d_{ij}\right)^2+
\sum_j\left(\sum_i d_{ij}\right)^2+
\sum_{ij}(1-hK_{ij})^2\right).$$

Lean 将矩阵表示和上式中的整数系数逐项对齐。逐一检验 $2^9$ 个 $d$ 和两个 $h$ 给出 $a\ge-72$、$b\ge-27$。因此在任何 $t>L$ 处，

$$\det(tI-H_s)\ge t^4-30t^2-72t-27=(t+3)^2(t^2-6t-3)>0.$$

厄米谱定理给出 $\langle w|H_s|w\rangle\le L\langle w|w\rangle$。取 Liu 等的矢量 $w=(0,-1+i\sqrt3,\sqrt3-i,2)$，它的模平方为 12，归一化后有 9 个非恒等 Pauli 期望的绝对值等于 $1/3$，另外 6 个等于 $1/\sqrt3$。绝对值之和恰好是 $3+2\sqrt3$。

## 640 个极端符号与极值态

在 $t=L$ 时，行列式等于 $(a+72)L+(b+27)$。取零等价于 $a=-72$ 且 $b=-27$。全体 1,024 种 $(d,h)$ 中恰有 20 种满足这两个等式。对每个 $(d,h)$ 任意指定 $u$ 的三个分量和 $v$ 的前两个分量，便能唯一恢复最后一个 $v$ 分量和全部 $C$。因此 32,768 个带符号矩阵恰有 $20\times32=640$ 个以 $L$ 为特征值。

独立的标准库 Python 脚本用高斯整数重算了全部 32,768 个四阶行列式和三次迹，总计得到 12 种特征多项式。脚本逐步作用五个 Clifford 生成元，还验证这 640 个符号向量恰好形成全正符号向量的轨道。这给出物理极值态的完整分类。单比特 Bloch 向量为 $(1,1,1)/\sqrt3$ 的两个态的乘积达到全正符号界，且每个非恒等 Pauli 的期望都非零。640 个取等矩阵的最高特征值都是单根，因为它们具有特征多项式 $(t+3)^2(t^2-6t-3)$。因此每个符号矩阵对应唯一极值射线，非零期望又保证不同符号对应不同射线。全部极值态是这两个单比特 $T$ 型态乘积的 Clifford 轨道。Shen 等在另两种魔性度量的研究中已识别出这个轨道，并给出其中 64 个乘积态及 576 个纠缠态的划分。[Shen、Yin、Zhang，式 (9)–(10) 及附录 D](https://arxiv.org/html/2611.08586#S3)

| 证据 | 核验范围 |
|---|---|
| `signed_rayleigh` | 任意符号，任意四维复向量，包括未归一化向量的齐次二次型上界。 |
| `footnote_norm` | 原论文脚注的复向量及其 Pauli 期望，直接证明达到精确值。 |
| `stabilizer_norm_maximum`、`half_entropy_maximum` | 对全部物理纯态给出 `IsGreatest`。 |
| `count_extremal_signs` | Lean 证明恰有 640 个签名使 $\det(LI-H_s)=0$。 |
| `check.py` | 整数穷举全部符号，核对 12 种特征多项式及其重数，核对 640 个最优符号构成单个 Clifford 轨道。纯态轨道的分类结合该穷举与上述单根论证。 |

## 复现

在 Lean 4.24.0 与 mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` 的 Lake 项目中运行

```sh
lake exe cache get Mathlib.LinearAlgebra.Matrix.PosDef Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs Mathlib.LinearAlgebra.Matrix.Notation Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.Field Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Tactic.FinCases Mathlib.Tactic.Positivity Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.Push
lake env lean -DwarningAsError=true StabilizerHalf.lean
python3 check.py
```

Lean 源码只依赖 mathlib。核心定理以 `#print axioms` 核对，输出为 `propext`、`Classical.choice`、`Quot.sound`。用于固定尺寸符号枚举的 `decide +kernel` 接受 Lean 内核检查。Python 使用标准库，所有谱与轨道检验用整数对表示高斯整数。

## 查重记录

- Liu 等明确点名半阶，给出数值候选态。Liabøtrø 的式 (78) 以量子随机访问码语言提出等价谱界，对两比特的所有 32,768 个矩阵做过数值本征值计算。2017 年的耦合符号构造已经严格给出可达下界。这里的精确上界和计数依赖于独立推导的四阶特征多项式。[Liu 等原稿](https://arxiv.org/abs/2502.17550) · [Liabøtrø 原论文](https://doi.org/10.1103/PhysRevA.95.052315)
- 查询 TrureTuring 的问题、公开 PR 和合并源文件。其三比特反例达到 21；该项目还明确把两比特的 $3+2\sqrt3$ 标为 NumPy 数值结果。另一条公开 Claude、Codex 和 GPT 多智能体工作研究相同的带符号矩阵，但优化跨符号的最大最小特征值，以求混态 Pauli-flat 最优纯度。该项目给出了此不同目标的六个对易情境奇偶证书。检索到的原始记录分别核对过量词和谱端点。[三比特原始工作议题](https://github.com/the-omega-institute/trureturing/issues/11468) · [三比特合并 PR](https://github.com/the-omega-institute/trureturing/pull/11504) · [作者标注的两比特数值结果](https://www.trureturing.org/research/liabotro-2017-signed-pauli-sum-norm/) · [另一项混态最优纯度研究](https://github.com/the-omega-institute/trureturing/issues/22656)
- 复核了近期两比特多种魔性度量、末端谱的量子随机访问码和 Clifford 对称态的工作。Shen 等的强度量极值分类包括同一集合的 640 个态；他们的稳定子 Rényi 熵证明针对二阶。Casaccino、Galvão、Severini 关于四维相空间算符的谱枚举使用适配选定完全 MUB 的符号约束。这里考虑全部任意符号。[Shen 等](https://arxiv.org/abs/2611.08586) · [量子随机访问码后续研究](https://arxiv.org/abs/2611.26705) · [Clifford 对称态分析](https://arxiv.org/abs/2512.19657) · [相空间算符谱](https://arxiv.org/abs/0805.3466)
- 检索词覆盖作者名、论文号、`signed Pauli sum`、`two-qubit stabilizer norm`、`3+2 sqrt(3)`、`640`、`1.866`、`maximal magic` 及 `all signs`。查过 GitHub 代码和 Issues、两比特开放问题目录当前分支及公开 PR、MathDB 和 EulerSolve 公开索引。Hexagon 站内 `signed Pauli sum` 返回 0 条。在可访问的这些记录中，未找到相同两比特全局谱上界的严格证明。该检索不能排除不同术语、未索引资料或私人结果。[GitHub 代码](https://github.com/search?q=%22SignedPauliSumNormRefutation%22+%22two-qubit%22&type=code) · [GitHub Issues](https://github.com/search?q=%22stabilizer+norm%22+%22maximal+magic%22&type=issues) · [开放问题目录及分支](https://api.github.com/repos/jpbruneton/open_quantum_problems/branches) · [Hexagon](https://hexagonmath.org/search?q=signed+Pauli+sum) · [MathDB 检索](https://www.google.com/search?q=site%3Amathdb.com+Liabotro+signed+Pauli+two+qubits+stabilizer+norm) · [EulerSolve](https://www.eulersolve.org/papers/)

研究与查重截至 2026 年 11 月 27 日。
