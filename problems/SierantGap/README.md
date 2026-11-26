# 非局域稳定子 Rényi-2 熵的计算基差距至多为 2 比特

令 $|\Psi\rangle$ 为有限个量子比特上的归一化二分纯态，$|\Psi_{\rm CB}\rangle=\sum_j\mu_j|j\rangle_A|j\rangle_B$ 为 Schmidt **振幅**按二进制标签降序排列的代表态。令 $M_{\rm CB}=M_2(\Psi_{\rm CB})$，$M_{\rm NL}$ 为 $M_2$ 在两个子系统各自所有酉变换下的最小值。对任意系统大小、二分方式及 Schmidt 谱，有

$$0\le M_{\rm CB}-M_{\rm NL}\le 2\quad\text{比特}.$$

Sierant 的定理 3 给出上界 4 比特。Lean 直接证明了新的有限群计数界，并用论文已证的矩阵迹关系推出两比特界。E27 将降低这个常数列为公开中间目标。下面证明的改进使用 Rényi 阶数 2 和底数 2。最优常数尚未确定。原文猜想 1 对应常数 0。[Sierant v2，定理 3 与式 (56)](https://arxiv.org/html/2609.13106v2) · [Open Quantum Problems E27](https://open-quantum-problems.vercel.app/p/E27)

## 八个初段的计数

在 $G=\mathbb F_2^n$ 中，用普通二进制将元素标为 $0,\ldots,2^n-1$。给定八个整数宽度 $1\le r_i\le 2^n$，记 $C(r)$ 为满足 $L_i(x,u,v,y)<r_i$ 的四元组数量，其中加法是按位异或，八个线性形式依次为

$$x,\ x+u,\ x+v,\ x+u+v,\ y,\ y+u,\ y+v,\ y+u+v.$$

在单个二进制位上，若四个选中行的输出可独立指定，它们就组成一个坐标基。定义 $B(r)$ 为在所有这些基上取到的最小宽度乘积 $\min_I\prod_{i\in I}r_i$。本次形式证明的核心不等式是

$$B(r)\le 4\,C(r).$$

**第一步。** 对任意二幂宽度 $R_i=2^{k_i}\le2^n$，有

$$C(r)\ \ge\ C(R)\prod_{i=1}^8\min(1,r_i/R_i).$$

先把各 $r_i$ 裁到 $R_i$。固定最低位后，某一行可用的高位标签数分别是 $\lceil r_i/2\rceil$ 和 $\lfloor r_i/2\rfloor$。若 $R_i=1$，相应输出位被固定为零，所有符合条件的输入列组成一个子群 $H$。对于 $H$ 上的任意二元线性测试 $\ell$，至少一半的列满足 $\ell=0$。把每个两点因子写成 $a_i+d_i1_{\ell_i=0}$，其中 $a_i,d_i\ge0$。按因子个数归纳，在 $H$ 与 $\ker \ell\cap H$ 上分别应用归纳假设，得到

$$\frac1{|H|}\sum_{z\in H}\prod_i(a_i+d_i1_{\ell_i(z)=0})\ \ge\ \prod_i(a_i+d_i/2).$$

被固定的位取 $d_i=0$。其余位上，两个高位计数的平均为 $r_i/2$。按比特数归纳即得矩形不等式。Lean 的 `direct_count` 证明递推值等于对全部输入位串的直接计数。

**第二步。** 按 $r_i$ 从小到大排列各行，同宽时用固定顺序。若一行在此前所有行均为零时还可能取 1，就把它加入基 $I$。这个基的输出可任意指定。对任意保持秩顺序的二幂取整，未选行的限制由更早的基行蕴含，因此 $C(R)=\prod_{i\in I}R_i$。Lean 构造了这个基并验证了双射与计数恒等式。

**第三步。** 写 $\log_2 r_i=a_i+u_i$，$a_i$ 为整数，$0\le u_i<1$。取一个所有行共用、在 $[0,1]$ 上均匀分布的阈值 $t$。当 $t<u_i$ 时令 $R_i=2^{a_i+1}$，其余时候令 $R_i=2^{a_i}$。该取整保持各秩的顺序，故第二步的基对每个 $t$ 都适用。把第一步代入 $\log_2(\prod_{i\in I}r_i/C(r))$，所得上界中，基行向下取整时贡献 $u_i$，基外行向上取整时贡献 $1-u_i$，其余贡献零。每行的平均贡献都是 $u_i(1-u_i)\le1/4$。八行共至多 2，取二的幂即得目标不等式。这里平均的是各阈值给出的同一个上界目标，八个取整决定共享一个随机数。

## 从论文矩阵恒等式到物理结论

下表将 `entropy_gap_le_two` 的参数对应到物理定义。由 Lean 重新验证的是此前未知的组合界，以及在下列已发表算子结果之上的求和、优化和熵换算。源文件不建立复矩阵 Pauli 算子的表示。引用中的方程与引理编号均采用 v2。[Sierant 全文](https://arxiv.org/html/2609.13106v2)

| Lean 参数或对象 | 在论文中的代入及依据 |
| --- | --- |
| `n`, `mu`, `sorted`, `nonzeroGap` | 平衡二分时两边各有 $n$ 比特，$d=2^n$。取 $\mu_0\ge\cdots\ge\mu_{d-1}\ge\mu_d=0$ 为 Schmidt 振幅及末尾的零。归一化保证至少有一个严格下降。第 II.1 节式 (2)–(5) 定义二阶稳定子熵、局部酉优化和排序代表态。 |
| `V`, `ref` | 取 $V=U(d)$，`ref` 为恒等酉。第 III.3 节引理 1 的式 (22)–(26) 以 Cauchy–Schwarz 证明原来的独立 $V_A,V_B$ 优化与单一 $V$ 的 $\max_V G_\mu(V)$ 相等。这一步允许任意局部酉。 |
| `K`, `pureSum` | 对秩为 $r$ 的前缀投影 $E_r$，令 $E_r(V)=VE_rV^\dagger$。由 $M=\sum_{r=1}^d (\mu_{r-1}-\mu_r)E_r$ 的逐对角元望远镜求和，任意谱都可作此展开。把它代入式 (30) 的四副本矩阵迹，分别展开两份四阶张量，正好得到八个非负差量的乘积。第 IV.2 节式 (32)–(33) 在二幂台阶上写出了同一多线性展开。一般秩允许全部 $r=1,\ldots,d$；`width` 将 Lean 的零起始索引转为此秩。`K V q` 等于 $d^2\operatorname{Tr}(X_\alpha(V)X_\beta(V))$，并且 `pureSum delta (K V)` 恰为 $G_\mu(V)$。 |
| `caps` | 附录 A.2 引理 3、5 的式 (83)、(85) 对任意整数秩、任意该秩正交投影都成立。每个乘以 $d^2$ 的迹满足八个交叉乘积与十二个去掉一副本的乘积上界。后十二式各有两个独立的最小值，其右端是四个所选乘积的最小值，所以该上界分别蕴含这四个乘积上界。附录 A.3 引理 7 枚举所有 56 个基。Lean 的 `rowBasis_mem_supports` 再次检验每个基都落在上述乘积中。`PublishedRankCaps` 正是这族逐秩乘积上界。 |
| `refTrace`, `cbKernel` | 附录 A.3 式 (86)–(87) 在任意秩给出 $d^2\operatorname{Tr}(X_\alpha(1)X_\beta(1))=C(r)$，与前一行的缩放完全相消。只有随后识别二幂秩子空间的部分要求二幂秩。 |
| `sSup`, `entropy2` | 每个秩项由 Lean 得到 $K(V,r)\le4C(r)$。用非负 Schmidt 差乘积加权，$G_\mu(V)\le4G_\mu(1)$；恒等酉可行，又有 $G_\mu(1)\le\sup_VG_\mu(V)$。式 (2)–(4) 给出 $M=-\log_2F$，故 $M_{\rm CB}-M_{\rm NL}=\log_2(F_*/F_{\rm CB})\in[0,2]$。Lean 证明参考纯度严格为正并处理上确界。 |

**不等分割。** 依第 III.1 节式 (16) 的第一、第三、第四步，以 $|0\rangle$ 将较小一侧补齐。补齐后的局部酉最小化包含原来所有在辅助比特上作用为恒等的变换，所以 $M_{\rm NL}(\Psi)\ge M_{\rm NL}(\Psi')$。附加零态对 $M_{\rm CB}$ 的贡献为零。于是原态的差距至多为补齐态的差距，后者已由平衡情形控制；原态计算基代表自身可行给出下界零。这里不使用式 (16) 中以猜想 1 为条件的中间等号。[第 III.1 节与引理 1](https://arxiv.org/html/2609.13106v2)

## 独立算例与复验

[标准库 Python 检查](check.py) 在 $n=2$ 的 $4^8=65536$ 组秩上，直接枚举 $(x,u,v,y)$ 的异或标签，通过八维前缀和求所有 $C(r)$，并独立识别 56 个四行基。最大 $B(r)/C(r)$ 为 $9/5$；宽度 $(3,3,3,3,3,3,3,1)$ 时，$B=27,C=15$。在 $n=3$、八个宽度全为 5 时，直接枚举得 $C=313,B=625$。二者是秩项比较的数值，不是熵差的测量。

文件中的七项 `#print axioms` 输出仅含 `propext`、`Classical.choice`、`Quot.sound`。八路形式的支持集归类通过内核计算完成，通用的比特数和秩界由归纳与实分析证明。[Lean 证明](SierantGap.lean)

## 已公开工作的核查

2026-11-27（中国时间）按论文编号、物理量的等价名称、旧常数与新常数、八项配置和二幂秩分别检索。原文定理 3 给出的常数为 4，E27 修改后的公开条目仍将其改进列为开放目标。Liu–Cui 证明某些整数阶下有序 Schmidt 代表是局部极小点，并给出其他谱界；文中未找到此处的全局两比特差距。[原文](https://arxiv.org/html/2609.13106v2) · [E27](https://open-quantum-problems.vercel.app/p/E27) · [Liu–Cui](https://arxiv.org/html/2609.01993v2) · [arXiv 题名检索](https://arxiv.org/search/?query=%22nonlocal+stabilizer+entropy%22&searchtype=all)

GitHub 发现 Chain.Ren 的公开排序证明。其定理覆盖所有整数阶、任意幅度置换与相位，并推出局部单项酉的精确最优性。该仓库不处理一般局部酉的加性误差。Huczynska、Rakhmonov、Yip 的二元群压缩论文研究加法表示计数的主序，这里引用其作为相关方法的先行工作。本证明用二元输出线性测试的核计数处理任意八行初段，再用共同阈值平均缩小误差。[Chain.Ren 的固定版本](https://github.com/Asakitan/monomial-stabilizer-renyi-rearrangement/blob/proof-v1.0.0/PROOF.md) · [二元群上的主序](https://arxiv.org/abs/2609.07855)

GitHub 代码、研究仓库及其可检索讨论中，定向查了 “Sierant / dyadic / gap / stabilizer”, “2609.13106 / factor four / sixteen”, “two-bit / Schmidt / dyadic”, “cubeRows / Sierant / entropy rounding”等组合。相关命中包括论文订阅摘要和上述单项酉证明。另查到 TrureTuring #23105 的 AI 研究预注册，题目是 Rényi 阶数 1/2 的 Schmidt 代表饱和性；该记录的命题与这里的二阶加性常数不同。还检索了 MathDB、EulerSolve 的公开索引及近期 arXiv 研究；核查到的后续文章讨论资源预算、费米子或动力学。在这次公开检索的可见结果中，尚未找到同一普适常数或相同的八行计数推论。未索引、私有或以不同术语发表的工作仍可能存在。[GitHub 原编号代码检索](https://github.com/search?q=%222609.13106%22+%22factor+four%22&type=code) · [GitHub 方法代码检索](https://github.com/search?q=%22Sierant%22+%22dyadic%22+%22gap%22+%22stabilizer%22&type=code) · [GitHub 讨论检索](https://github.com/search?q=%222609.13106%22+%22entropy%22&type=issues) · [TrureTuring #23105](https://github.com/the-omega-institute/trureturing/issues/23105) · [MathDB 定向检索](https://www.google.com/search?q=site%3Amathdb.com+%22Spectral+geometry+of+nonlocal+stabilizer+entropy%22) · [EulerSolve 定向检索](https://www.google.com/search?q=site%3Aeulersolve.com+Sierant+stabilizer+entropy) · [资源预算](https://arxiv.org/abs/2609.31841) · [费米子](https://arxiv.org/abs/2611.07003) · [动力学](https://arxiv.org/abs/2609.18691)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.GroupTheory.Index Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Data.ZMod.Basic Mathlib.Data.Fintype.BigOperators Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Data.Real.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.FieldSimp Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.Tactic.NormNum Mathlib.Analysis.SpecialFunctions.Log.Base Mathlib.Data.Fintype.EquivFin Mathlib.Data.Fin.VecNotation Mathlib.Tactic.FinCases
lake env lean -DwarningAsError=true SierantGap.lean
python3 check.py
```
