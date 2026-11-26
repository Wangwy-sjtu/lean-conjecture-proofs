# 两比特 WH–MUB 极值从二阶推广到所有实数阶

对于任意两比特纯态和每个实数 $\alpha\ge2$，稳定子 Rényi 熵的最大值为

$$\frac{1}{1-\alpha}\log\!\left(\frac{1+3\,4^{1-\alpha}}{4}\right).$$

取自然对数，熵单位是 nat。恰有 480 个相差全局相位视为同一态的极值态，组成 $(1,i,i,i)/2$ 的两比特 Clifford 轨道。此结果回答 Liu、Low、Yin 正式猜想中 $n=2$ 的全部有限实数阶。原猜想还包括其他没有 Weyl–Heisenberg SIC 的系统。[原论文第 4 页，式 (21) 后的 Conjecture](https://arxiv.org/pdf/2502.17550#page=4) · [期刊版本](https://doi.org/10.1088/2058-9565/ae3028)

这是 Shen、Yin、Zhang **已证二阶定理的推论**。Lean 核验从二阶定理到任意实数阶的推导、实际 Pauli 期望的纯度恒等式以及达到上界的显式态。二阶估计在代码中是显式前提 `orderTwoBound`，二阶等号分类是 `orderTwoEquality`。原作者提供的 751 阶有理半正定证书未在本包内用 Lean 重新验证。[Shen 等，式 (1)、第三节及附录 C](https://arxiv.org/html/2611.08586#A3) · [作者原始证书和说明](https://arxiv.org/abs/2611.08586#anc)

## 数学证明

令 $P$ 遍历 15 个非恒等两比特 Pauli 串，令 $q_P=|\langle\psi|P|\psi\rangle|^2$。归一化纯态的 Pauli 展开给出 $\sum q_P=3$。Shen 等证明 $M_2\le\log_2(16/7)$。他们的式 (1) 是 $-\log_2[(1+\sum q_P^2)/4]$，因而这恰好给出 $\sum q_P^2\ge3/4$，与对数底无关。其附录 C 的等号态是 Liu 等给出的 480 个态；它们在 15 个非恒等 Pauli 中有 3 个零重叠和 12 个模为 $1/2$ 的重叠。[二阶定理及其证书](https://arxiv.org/html/2611.08586#A3) · [480 态数据的原始说明](https://arxiv.org/src/2611.08586v1/anc/README.txt)

令 $p_P=q_P/3$。它们构成概率分布。对 $x^{\alpha-1}$ 使用 Jensen 不等式，对所有实数 $\alpha\ge2$ 有

$$\sum_P q_P^\alpha=3\sum_P p_P q_P^{\alpha-1}
 \ge 3\left(\sum_P p_Pq_P\right)^{\alpha-1}
 =3\left(\frac{\sum_P q_P^2}{3}\right)^{\alpha-1}
 \ge 3(1/4)^{\alpha-1}.$$

补回恒等 Pauli 的贡献 1，除以 4，取对数后再除以负数 $1-\alpha$，得到熵的上界。显式态 $(1,i,i,i)/2$ 对全部阶同时取等。任何二阶严格不等的态在上式最后一步都严格，所以新的等号态必是原论文的二阶等号态，而它们全部达到新界。对 $\alpha>2$ 还可直接用严格 Jensen 得出每个非零 $q_P$ 都等于 $1/4$。这个重叠分布的结论只用到二阶的数值下界；将其认作特定的 480 个物理态时可用原作者分类。[Liu 等，式 (17)–(21)](https://arxiv.org/pdf/2502.17550#page=3)

## Lean 声明和外部输入

| 声明 | 内容 |
|---|---|
| `size_biased_power`、`strict_transfer`、`flat_power` | 任意有限非负数组的通用不等式、严格性与等幅取等，不依赖物理文献。 |
| `weylSquare`、`labels_complete`、`purity` | 在 00、01、10、11 顺序下按 $X^x Z^z$ 计算模平方。相位 $(-1)^{z\cdot j}$ 和位异或位移各自逐项给出。四个归一复振幅用八个实数表示。Lean 逐项证明 15 个标签涵盖全部非恒等项，且它们总和为 3。 |
| `witness_flat` | 从实际振幅直接算出 $(1,i,i,i)/2$ 的每个非恒等 Pauli 模平方都为 0 或 $1/4$。 |
| `maximum_all_real_orders` | 以 `orderTwoBound` 为唯一文献前提，证明在所有两比特归一化纯态上的 `IsGreatest`，给出极值和达到极值的显式态。 |
| `entropy_eq_iff` | 使用 `orderTwoBound` 和 `orderTwoEquality`，得到 $\alpha\ge 2$ 的等号刻画。 |
| `entropy_eq_iff_above_two` | 只使用 `orderTwoBound`，对 $\alpha>2$ 用严格 Jensen 独立得到等号刻画。 |

作者原始辅助材料列出了 751 个单项式与 Gram 矩阵上三角的 18,736 个非零有理条目。按非零元的连通分量可拆成一个 151 阶块、十五个 28 阶块和十五个 12 阶块。其二阶证明还用到了原文所述十六次多项式恒等式。这里的 `#print axioms` 输出只有 `propext`、`Classical.choice`、`Quot.sound`。这项检查与上表中明确列出的定理前提各有不同的含义。[原始矩阵](https://arxiv.org/src/2611.08586v1/anc/M_entries.csv) · [单项式](https://arxiv.org/src/2611.08586v1/anc/monomials.csv) · [480 个候选态](https://arxiv.org/src/2611.08586v1/anc/maximizers.csv)

## 复现

使用 Lean 4.24.0 与同版本 mathlib，项目固定版本为 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。在对应 Lake 项目中运行

```sh
lake env lean MUBRealOrder.lean
python3 check.py
```

Python 使用标准库，从 5 个 Clifford 生成元构造 Pauli 向量的完整轨道，得到 480 个不同的精确向量。另外用 4 个纯态在三个整数阶验算有理不等式，在四个非整数阶作数值交叉检查。普遍的实数阶界由 Lean 中的凸性证明保证。

## 已公开结果核查

- Liu 等原论文明确提出全部实数阶的猜想。2026 年 11 月 5 日 Shen 等给出二阶数值与等号态的精确证明。Cuffaro 和 Fuchs 也曾用 Jensen 给出 SIC 情形的界，使用所有非对角重叠的等权分布。此处权重为非恒等 Pauli 的模平方，并使用已有两比特二阶下界来处理其中允许零项的 WH–MUB 分布。[原猜想](https://arxiv.org/abs/2502.17550) · [二阶论文](https://arxiv.org/abs/2611.08586) · [Cuffaro 和 Fuchs，第 IV 节](https://arxiv.org/pdf/2412.21083#page=5)
- 开放问题 E28 目录仍标为待解。查了维护者仓库当时的完整文件树、所有现存分支与全部 19 个公开 PR。PR #16 的 ququart MUB 笔记讨论五组测量的 Shannon 熵。另检查公开 AI 仓库 `physical-superintelligence/oqp-batch-2026` 的 3 个分支、3 个 PR 和项目列表。当前目录中未找到这里的二阶到全实数阶推论。[E28](https://open-quantum-problems.vercel.app/p/E28) · [目录仓库固定版本](https://github.com/jpbruneton/open_quantum_problems/tree/9eb057b006c802ff25016656d7b1c12fe8b46230) · [目录的全部 PR](https://github.com/jpbruneton/open_quantum_problems/pulls?q=is%3Apr) · [目录分支](https://api.github.com/repos/jpbruneton/open_quantum_problems/branches) · [具体的 Shannon 熵工作](https://github.com/jpbruneton/open_quantum_problems/pull/16) · [AI 批量项目](https://github.com/physical-superintelligence/oqp-batch-2026/tree/e5dd29ca987a15c883f3a19a97372acf155b617c) · [AI 项目分支](https://api.github.com/repos/physical-superintelligence/oqp-batch-2026/branches)
- 代码检索实际命中 HugoWEI 的三 T 门电路与既有 480 态轨道的精确距离证明，以及 Tavis Rudd 的奇素数维立方相位态二阶魔性文献核查。HugoWEI 仓库当时只有 main 分支且无公开 PR。这两份记录都引用 Liu 等的二阶结果。[电路轨道距离原文](https://github.com/HugoWEI/quantum-magic-gate-bounds/blob/3edc23b80cd61ac91ecd5aaae5602b259ad648a3/notes/exact_maximal_magic_orbit_proximity.md) · [立方相位态文献核查](https://github.com/tavisrudd/othello/blob/1c96b58ddb59a22a44fff092c7ffe3da18a22e7c/notes/2026-09-07-c1099-lit-check-magic-of-phase-states.md)
- 检索了两篇原文编号与作者姓名、`two-qubit maximal magic`、`MUB fiducials`、`all orders`、`Jensen`、`16/7` 的组合，并查询 GitHub Issues 与代码。两个论文编号的 GitHub Issues 联合查询命中一条论文推荐。Hexagon 站内精确组合返回 0 篇。TrureTuring 当时的 2,235 项公开成果目录中命中另一项两比特非局域非稳定子性问题。MathDB、EulerSolve 的站点范围检索未找到本推论。这些结果覆盖公开且能访问的记录，无法排除未索引手稿、不同术语或私人工作。[GitHub Issues](https://github.com/search?q=%222502.17550%22+OR+%222611.08586%22&type=issues) · [GitHub 代码](https://github.com/search?q=%22maximal+magic%22+%22Jensen%22+%22MUB%22&type=code) · [Hexagon](https://hexagonmath.org/search?q=two-qubit+maximal+magic) · [TrureTuring 公共目录](https://the-omega-institute.github.io/trureturing-pages/assets/research-catalog.json) · [MathDB 范围检索](https://www.google.com/search?q=site%3Amathdb.com+two-qubit+maximal+magic+MUB+Jensen) · [EulerSolve 范围检索](https://www.google.com/search?q=EulerSolve+two-qubit+maximal+magic+MUB+Jensen)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Analysis.MeanInequalitiesPow Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.Field Mathlib.Data.Fin.VecNotation Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true MUBRealOrder.lean
```
