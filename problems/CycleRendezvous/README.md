# 环图上一步相遇的最优经典与量子概率

两名玩家在同一个有标号的环 $C_N$ 上独立均匀抽取起点，可抽到同一点。每人只看自己的起点，必须沿一条边移动一步。移动结束时占据同一顶点即获胜。这个约定对应 Tucker、Strange、Mironowicz 和 Quintanilla 论文中 $W=0,S=1,E=0$ 的 *check-later* 游戏。[论文第 2 节及第 3.2 节](https://kar.kent.ac.uk/107718/1/Tucker_2024_New_J._Phys._26_093038.pdf)

对每个整数 $N\ge3$，记 $\delta_N=0$ 当 $4\mid N$，$\delta_N=2$ 当 $N\equiv2\pmod4$，其余情形 $\delta_N=1$。最优成功概率为

$$
p_{\mathrm C}=\frac{2N-\delta_N}{N^2},\qquad
p_{\mathrm Q}=\frac{3+\cos(\pi\delta_N/N)}{2N}.
$$

经典玩家可以事先约定不同策略并共享随机性。量子上界允许任意维数和任意二元局域测量，一个 Bell 对和显式的单比特测量即达到上界。量子优势严格为正恰在 $4\nmid N$。两种最优策略之比满足

$$
1\le \frac{p_{\mathrm Q}}{p_{\mathrm C}}\le\frac{N}{N-1},
\qquad \lim_{N\to\infty}\frac{p_{\mathrm Q}}{p_{\mathrm C}}=1.
$$

原论文 §3.2.1 猜想每次都去标签较小的邻居是最优经典策略。这个规则在 $3\le N\le6$ 达到最优，所有 $N\ge7$ 都严格落后。原文公式 (12) 准确计算该指定规则，(21) 准确给出量子侧的渐近常数。两种最优策略都有 $Np\to2$，因而 (21) 下关于 *check-later* 最优值相差二倍的比较需要修正。[期刊全文与表 2](https://kar.kent.ac.uk/107718/1/Tucker_2024_New_J._Phys._26_093038.pdf)

| 环长 | 较小邻居规则 | 经典最优 | 量子最优 |
|---:|---:|---:|---:|
| 5 | $9/25$ | $9/25$ | $(3+\cos(\pi/5))/10$ |
| 6 | $5/18$ | $5/18$ | $7/24$ |
| 7 | $11/49$ | $13/49$ | $(3+\cos(\pi/7))/14$ |
| 8 | $3/16$ | $1/4$ | $1/4$ |
| 9 | $13/81$ | $17/81$ | $(3+\cos(\pi/9))/18$ |

Mironowicz 在 2023 年发表的表 IV 已用穷举得到 $N=7,8,9$ 的经典最优数值，也给出这些尺寸的量子数值。2026 年 Tucker 等人在环图系综论文中明确提及 $C_7$ 的最优经典策略发生变化。这些有限反例和数值属于在先研究。2024 年论文公式 (20) 已给出任意环长的单参数量子协议。本条目给出从原胜负规则到已知圈上 XOR 优化的归约、全尺寸精确经典值，以及对任意量子策略的匹配上界。[2023 年表 IV](https://arxiv.org/pdf/2207.14404) · [2024 年公式 (20)](https://arxiv.org/pdf/2405.14951) · [2026 年系综论文](https://arxiv.org/pdf/2606.16784)

## 从相遇事件到圈上的二染色

用 $+1$ 和 $-1$ 表示两种行走方向。若两位玩家的二元输出期望是 $a_x,b_y$，乘积期望是 $C_{xy}=\operatorname{Re}\langle u_x,v_y\rangle$，按最后占据的顶点统计四种移入方式，单方期望在对所有顶点求和后抵消。于是

$$
N^2p=N+\frac14\sum_{x\in\mathbb Z/N}
  \operatorname{Re}\langle u_x-u_{x+2},v_x-v_{x+2}\rangle .
$$

将概率乘以 $N/2$ 后，右式正是以下二染色游戏的胜率。以 $1/2$ 的概率询问同一顶点，要求两人给出相同颜色。各以 $1/4$ 的概率询问间隔 $+2$ 或 $-2$ 的顶点，要求异色。步长二的置换有 $\gcd(N,2)$ 个分量，每个含 $m=N/\gcd(N,2)$ 个顶点。$N=4$ 的两个方向在同一邻点合并，各自的权重仍计入。对奇数 $m$，Helton 等人定理 5.3 的对称输入分布取 $p=q=1/2$，恰给出无同步限制的值 $(3+\cos(\pi/m))/4$。偶数 $m$ 可二染，胜率是 1。因此归约完成后，量子优化已由既有定理覆盖。Lean 使用有限 Fourier 变换直接重证这个值。[Helton 等人，定理 5.3](https://arxiv.org/pdf/2109.14741)

经典情形取 $u_x,v_x\in\{-1,1\}$。不等式 $2\operatorname{Re}\langle a,b\rangle\le\lVert a\rVert^2+\lVert b\rVert^2$ 将任意两套局域策略的得分控制在同策略情形的最大值。每个奇长分量至少有一条边两端同色，每个偶长分量可让所有边两端异色。一共恰好需要 $\delta_N$ 条同色边。两个玩家沿原始标签 $0,\ldots,N-1$ 都采用 $++--++--\cdots$ 的方向规则，即达到经典最优。

量子情形取 $u_x=A_x\psi,\ v_y=B_y\psi$。二元局域 POVM 给出自伴收缩 $A_x,B_y$，因此所有这些向量的范数都至多为 1。令 $D f(x)=f(x)-f(x+2)$，Fourier 变换给出 $D^*D$ 的最大特征值 $2+2\cos(\pi\delta_N/N)$。在 $\lvert\Phi^+\rangle=(\lvert00\rangle+\lvert11\rangle)/\sqrt2$ 上，令 $k=\lfloor(N+2)/4\rfloor$，$z_x=\exp(2\pi i kx/N)$。Alice 的基向量为 $(\lvert0\rangle\pm z_x\lvert1\rangle)/\sqrt2$，Bob 使用相位 $\bar z_y$。这给出最高 Fourier 模式，并达到上界。上界证明也适用于无限维 Hilbert 空间中的交换算子模型。混合态可用纯化或向量态表示处理。

## Lean 与独立核验

源码只依赖 Lean 4.24.0 及 mathlib v4.24.0，mathlib 提交为 f897ebcf72cd16f89ab4577d0c826cd14afaafc7。

| 声明 | 结论 |
|---|---|
| meeting_from_starts、meeting_identity | 由所有有序起点和四种输出的胜负谓词推出差分恒等式 |
| classical_optimum、mixture_bound | 任意两套确定策略的匹配上下界与有限共享混合上界 |
| lowest_rule_loses_iff | 直接按两邻点的数值标签做决策，证明该规则严格落后当且仅当环长至少为七 |
| quantum_upper | 任意复内积空间上通过算子 Born 表达式给出的策略上界 |
| qubit_orthonormal、bell_normalized、bell_from_qubits、bell_attains | 局域测量基的正交归一、Bell 态的归一、张量积振幅及可达性 |
| advantage_iff、ratio_window、optimal_ratio_limit | 严格优势的完整分类、有限尺寸界和极限 |

任何共享随机变量在有限输入输出上诱导有限个确定策略对的分布。私有随机也可一并预采样，因此混合界覆盖经典随机局域策略。无限维上界使用复内积空间的向量范数及局域算子对纯态向量的作用。标准密度算子到向量态的纯化属于这里使用的量子力学背景。

在已安装上述版本依赖的 Lake 项目中运行以下命令，文件路径按保存位置调整。源码末尾打印主要定理的公理依赖，核验输出随源码保存。

~~~sh
lake env lean CycleRendezvous.lean
python3 check_cycle.py
~~~

Python 脚本从起点直接计算每种 Alice 决策下 Bob 的最优应答，在 $3\le N\le15$ 枚举 65,528 种 Alice 决策，覆盖 1,431,655,744 对确定策略。它也直接收缩二比特乘积测量振幅，在 $3\le N\le41$ 检查每对输入的归一及相遇胜率，并在 $3\le N\le1024$ 检查所有 Fourier 模式。经典计数使用整数，后两项为浮点复核。全尺寸结论由 Lean 证明。

## 在先工作与检索范围

- Braunstein–Caves 的链式不等式、Wehner 的最优 Tsirelson 界，以及 Cleve–Høyer–Toner–Watrous 的单向奇环游戏都是既有结果。后者只抽取同点或向前的一个邻点，其无约束最优值为 $\cos^2(\pi/(4m))$。与本题归约精确相符的是 Helton 等人定理 5.3 的双向对称抽样；其定理 5.2 还给出了相同数字的定向游戏同步值。[Braunstein–Caves](https://www-users.york.ac.uk/~sb54/papers/90/bcB90.pdf) · [Wehner](https://arxiv.org/abs/quant-ph/0510076) · [Cleve 等人 §3.2 及推论 9](https://arxiv.org/abs/quant-ph/0404076) · [Helton 等人 §5](https://arxiv.org/pdf/2109.14741)
- 按三篇 rendezvous 论文的标题、编号、作者、check-later、lowest-indexed neighbour、对称奇环 XOR、circulant Laplacian、synchronous MaxCut 与等价余弦值检索论文、作者主页和公开索引。原论文所链接的 Kent 数据压缩包有 66 项，目录中为胜负及电路实验的 .pkl 与 .txt 文件。2026 年作者团队的全文和补充资料研究图系综，并讨论了若干单环作为对照。检索到的资料中没有将上述归约、两端最优值和渐近更正一并用于原游戏的公开文稿。[Kent 数据](https://data.kent.ac.uk/532/) · [Tucker 主页](https://research.kent.ac.uk/pqm/person/joshua-tucker-2/) · [2026 年全文及补充材料](https://arxiv.org/pdf/2606.16784)
- GitHub 默认分支代码检索使用论文号、标题、rendezvous 和 Mironowicz，另查全站 Issues、PR 及项目名。命中包括文献目录、量子电路图数据集和 TrureTuring 的 2026 年超立方体问题。后者固定两起点的汉明距离，每人一次翻转指定数目的坐标；其公开问题记录与分析针对该特定模型。AIM 的相近目录项研究隐藏标签排列下的多轮完全图，目标是最小化首次相遇的期望时间。[TrureTuring 原页及模型](https://github.com/the-omega-institute/trureturing/blob/dev/Problems/wang-2026-hypercube-rendezvous-quantum-gap.md) · [Wang 论文](https://arxiv.org/abs/2610.12949) · [AIM 候选原页](https://github.com/MColbrook/AIM/blob/b2ec0fac559f532fc0ed04fce81deea0ce07c68b/research/expansion-2026-09/candidates/symmetric-rendezvous-discrete-locations.json)
- 公开 Git 远端给出的分支名中，TrureTuring 有 12,436 个，solved-conjectures 有 13 个，AIM 有 22 个。按作者、游戏及奇环相关名称筛选，单独查阅了 TrureTuring 六个候选分支头。五个是 Porto 等人的 n-cycle 情境性权衡，另一个是超立方体 rendezvous。solved-conjectures 的该题 Issues 检索无匹配。MathDB 免费公开问题页和网页索引按作者、题名及同义表达式检索，未定位到该环图问题的 canonical 页。记录范围限于可检索材料和有指向的分支头，公开检索无法保证未公开或未索引材料的优先权。[n-cycle 候选分支头](https://github.com/the-omega-institute/trureturing/commit/9bb53715560ead9efafa1f6929ce191ec6f390d0) · [超立方体候选分支头](https://github.com/the-omega-institute/trureturing/commit/bd8ea7a079b866b0dfd6dc542cfde8127dd2550d) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Analysis.Fourier.ZMod Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true CycleRendezvous.lean
```
