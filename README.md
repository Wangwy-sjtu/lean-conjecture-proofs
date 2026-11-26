# 小猜想的 Lean 证明与反例

本仓库收录数学文献和整数数列条目中的附带猜想。每道题提供原始出处、已有结果、数学推导和可独立复验的 Lean 文件。证明探索和形式化使用了 AI 辅助。

| 问题 | 已经 Lean 验证的结论 | 下载 |
| --- | --- | --- |
| [A005558–A005562 · 象限随机游走](problems/A005562/) | 从四方向步的定义证明任意终点高度的二阶递推，同时覆盖五个已提出的固定高度公式 | [独立 ZIP](packages/A005562.zip?raw=1) |
| [A245690 · 素因子筛的取值与首次位置](problems/A245690/) | 每个正整数值都在一条无穷等差数列上出现。余数 6 的首次位置为 $7\cdot233\#$，其所有出现位置的最大公因数恰为 $233\#$ | [独立 ZIP](packages/A245690.zip?raw=1) |
| [A113572 · 按位置限制数位的倍数](problems/A113572/) | 完整刻画何时存在所需的 $n$ 位倍数，并证明一个对所有目标余数成立的有限长度覆盖定理 | [独立 ZIP](packages/A113572.zip?raw=1) |
| [A086004 · 十进制旋转加法](problems/A086004/) | 证明连续保持素性的最大次数恰为 4，四次实例中每一步的数值和素性均通过内核检查 | [独立 ZIP](packages/A086004.zip?raw=1) |
| [A001122 · 形如 $2^k+3$ 的素数](problems/A001122/) | $2^{2191}+3$ 为素数，但 2 的乘法阶严格小于 $p-1$ | [独立 ZIP](packages/A001122.zip?raw=1) |
| [A024399 · 基本对称函数之比](problems/A024399/) | 对所有下标证明七阶递推和生成函数的系数恒等式 | [独立 ZIP](packages/A024399.zip?raw=1) |
| [A347225 · 孪生素数的循环节](problems/A347225/) | 三对小于 6300 万的孪生素数具有相同正周期增量 1,120,174，落在原报告检验过的范围内 | [独立 ZIP](packages/A347225.zip?raw=1) |
| [A004613 · 平方三元组的解数](problems/A004613/) | 固定一坐标后恰有一个允许的解，证伪注释的两种读法 | [独立 ZIP](packages/A004613.zip?raw=1) |
| [A121285 · 对称凸 permutomino 的枚举](problems/A121285/) | 从已知组合计数闭式证明 Mathar 的四项递推，覆盖所有 $n\ge3$ | [独立 ZIP](packages/A121285.zip?raw=1) |
| [A088226 · 最近平方数的下标勘误](problems/A088226/) | 原注记在每个正平方数加 1 的下标处失效，从三项递推证明修正后的距离公式 | [独立 ZIP](packages/A088226.zip?raw=1) |

## 论文核心猜想的反例

Cao、Lu、Nie、Sun、Tian 提出，连通图能用 $m+n-1$ 个 CNOT 门实现全部边奇偶并恢复输入，当且仅当它有完美消去序。**七顶点图 $K_{1,3,3}$ 直接反驳逆向蕴涵。** 其 15 条边用 21 道门依次实现，全部线路恢复，而 5040 种顶点排列均不满足消去条件。同一张图的每一个完美网络还都必须使用全部七根线路作控制，回答了作者的问题 (C2)。证明包也给出无三角形图的完整分类、两类精确门数和一般的生成树必要条件。[逐门反例与数学证明](problems/GraphicParity/COUNTEREXAMPLE.md) · [Lean 与运行方法](problems/GraphicParity/) · [独立 ZIP](packages/GraphicParity.zip?raw=1) · [原作者稿猜想 18](https://yiren.lu/assets/pdf/parity-network.pdf#page=13)

## 论文点名的极值问题

对斐波那契砖长 $1,2,3,5,\ldots$，前 $n$ 项能排成多少行，使不同行的非空真前缀和互异？对所有正整数 $n$，最大高度恰为 $n$，仅在 $n=3,4,5$ 时为 $n-1$。当 $n\ge9$，同一个圆排列模板的所有轮换都可同时取用。这完整给出 Dębski 等人第 4 节所问的斐波那契情形。[数学说明与 Lean 文件](problems/FibonacciBarrycadeHeight/) · [独立 ZIP](packages/FibonacciBarrycadeHeight.zip?raw=1) · [原论文](https://arxiv.org/html/2609.18476v2#S4)

## 论文开放问题的部分进展

| 论文问题 | 已经 Lean 验证的结论 | 下载 |
| --- | --- | --- |
| [Alofi–Dukes · 随机沙堆的缺额多项式](problems/SandpileK3n/) | 对所有 $K_{3,n}$ 和任意吸收点，证明常返配置按总缺额计数的系数对数凹且单峰，并给出两种吸收点位置各自的计数公式 | [独立 ZIP](packages/SandpileK3n.zip?raw=1) |
| [Fazekas 等 · 二元词中的 Abel 平方](problems/FMMSFourLetterMinimum/) | 含四个 $a$ 和 $B\ge4$ 个 $b$ 时，不同 Abel 平方因子的最小数恰是 $1+\lfloor(B+2)/4\rfloor$。取等构造来自原文，此处证明任意排列的下界 | [独立 ZIP](packages/FMMSFourLetterMinimum.zip?raw=1) |
| [Cao 等 · 图奇偶网络的完美消去序](problems/Multipartite/) | 对所有完全多部图，精确求出最少补多少个全邻接顶点，以及在原顶点之间最少补多少条边。两个最优值相等 | [独立 ZIP](packages/Multipartite.zip?raw=1) |
| [Dębski 等 · 无限贪心 Barrycade 的遗漏数](problems/GreedyBarrycade/) | 每个非首行的永久遗漏数介于 $1$ 与 $r-1$ 之间；任意有限组行的位移最终共享一个周期。还证明第四行起若每行漏掉首项减一，则全部非首行都只有一个遗漏 | [独立 ZIP](packages/GreedyBarrycade.zip?raw=1) |

打开题目目录或解压相应 ZIP，在其中按 README 的命令运行。文件末尾的 `#print axioms` 输出可核对主定理的公理依赖。各题说明记录了检索日期和范围，公开优先权仍可能受未索引材料影响。

[逐题查重记录，包括 arXiv、GitHub 和公开 AI 证明库](PRIOR_ART.md)
