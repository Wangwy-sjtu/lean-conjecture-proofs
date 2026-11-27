# 数学与量子信息问题的 Lean 证明与反例

本仓库收录论文和整数数列条目中的公开问题。各条目提供原始出处、数学说明、Lean 源码和独立下载包。证明探索与形式化使用了 AI 辅助。[逐题查重与在先结果](PRIOR_ART.md)

## 代表成果

### 1. 图奇偶网络：七个顶点推翻猜想 18

**原论文问了什么？** Cao 等问，一个连通图若能用理论最少的 $m+n-1$ 个 CNOT 门实现全部边的奇偶量，并将每根线路恢复原样，它是否一定有完美消去序？这里 $m$ 是边数，$n$ 是顶点数。 [作者稿第 13 页](https://yiren.lu/assets/pdf/parity-network.pdf#page=13)

**我们证明了什么？** 答案是否定的。完全三部图 $K_{1,3,3}$ 的 15 条边用 21 个门就能全部实现，七根线路最终各自复原，但 5,040 种顶点排序都不满足消去条件。对任意无三角形图，加一个全邻接顶点后能达到门数下界，当且仅当原图的边可以分成两片森林。

[21 道门的逐步证书](problems/GraphicParity/COUNTEREXAMPLE.md) · [两片森林判据](problems/GraphicParity/ConeForests.lean) · [证明与代码](problems/GraphicParity/) · [下载 ZIP](packages/GraphicParity.zip?raw=1)

### 2. 非回溯随机游走：到达每个目标的平均时间都严格缩短

**原论文问了什么？** Breen 等在第 4 问中比较两种图上游走。若每一步禁止立即沿上一条边原路返回，按顶点首次命中时间定义的 Kemeny 常数，是否总比普通随机游走的小？ [原论文，第 5 节 Question 4](https://arxiv.org/html/2510.06650v1#S5)

**我们证明了什么？** 在有限无向简单图上，若最小度至少为 2 且相关命中时间的期望有限，则对每个固定目标，按平稳分布抽取起点时，非回溯游走的平均命中时间都严格更短。证明给出差值的平方和公式。再按平稳分布对目标取平均，即得原问题的严格不等式。

[证明与代码](problems/NonbacktrackingKemeny/) · [下载 ZIP](packages/NonbacktrackingKemeny.zip?raw=1)

### 3. Nim 堆与公平博弈：统一阈值恰为 ⌊d²/4⌋

**原论文问了什么？** Beideman、Bowen、Müyesser 在第 3 问中将一个固定局面与大小为 $k$ 的 Nim 堆作选择复合。一步可以走原游戏、减小堆，或两者同时进行。哪些局面会在堆充分大时达到 Grundy 值的上界？ [期刊原文，第 18–19 页](https://math.colgate.edu/~integers/ug4/ug4.pdf#page=18)

**我们证明了什么？** 每个有限局面都能达到。设从该局面出发最长还可走 $d$ 步，则只要 $k\ge\lfloor d^2/4\rfloor$，复合局面的 Grundy 值就恰为 $k+d$。每个深度都有达到这个阈值的局面，所以对同一深度的全部游戏，阈值不能再降低。

[证明与代码](problems/SelectiveCompound/) · [下载 ZIP](packages/SelectiveCompound.zip?raw=1)

## 其他完整解答与精确极值

| 成果 | 原问题 | 我们证明了什么 |
| --- | --- | --- |
| [Spiro、Surya、Zeng · 半受限博弈，第 22 与 23 问](problems/SemiRestricted/) · [ZIP](packages/SemiRestricted.zip?raw=1) | 第 22 问中的一般配额误差能否降到平方根阶？第 23 问中的等配额收益是否对每个含弧欧拉定向图都达到平方根阶？ [原文](https://doi.org/10.37236/11563) | 两问均成立。最大配额为 $M$ 时，均匀洗牌将相对最佳固定动作的收益增量控制为 $O_D(\sqrt M)$。在含弧欧拉定向图上，每个动作配额均为 $n$ 时，最优期望收益为 $\Theta_D(\sqrt n)$。 |
| [Liu–Low–Yin 与 Liabøtrø · 两比特半阶精确极值](problems/StabilizerHalf/) · [ZIP](packages/StabilizerHalf.zip?raw=1) | Liu、Low、Yin 指出的两比特纯态是否在半阶达到最大魔性？ [原文](https://arxiv.org/pdf/2502.17550#page=4) | 在所有两比特纯态上，半阶稳定子 Rényi 熵的最大值恰为 $2\ln(1+\sqrt{3}/2)$，原文指定的态达到该值。Liabøtrø 此前已给出数值枚举与取等构造，这里补全精确上界。 |
| [Levin · Band or Bump 停牌概率](problems/BandOrBump/) · [ZIP](packages/BandOrBump.zip?raw=1) | Levin 在 Remark 2 问，不放回抽牌时，恰在第 $n$ 抽因某类牌超出上限而首次停牌的概率，是否关于 $n$ 对数凹？ [原文](https://arxiv.org/pdf/2407.08062#page=7) | 对任意牌型数、每类张数和全部合法阈值都对数凹，并给出概率严格为正的全部时刻。 |
| [Dębski 等 · 斐波那契砖墙的最大高度](problems/FibonacciBarrycadeHeight/) · [ZIP](packages/FibonacciBarrycadeHeight.zip?raw=1) | 前 $n$ 个不同的斐波那契数最多能排成多少行，使每行都是一个排列且不同行的非空真前缀和互异？ [原文](https://arxiv.org/html/2609.18476v2#S4) | 除 $n=3,4,5$ 时最多排 $n-1$ 行外，其余正整数 $n$ 都恰好能排 $n$ 行。 |
| [Tucker 等 · 环图的一步相遇概率](problems/CycleRendezvous/) · [ZIP](packages/CycleRendezvous.zip?raw=1) | 两人在环上各走一步，以终点同点为胜。环长变化时，经典与量子策略的最佳相遇概率如何变化？ [原文](https://kar.kent.ac.uk/107718/1/Tucker_2024_New_J._Phys._26_093038.pdf) | 对每个环长求得移动后同点相遇的经典与量子最优值，从 $N=7$ 起原文选取较小标签邻居的规则严格落后。量子相对最优经典的倍率趋于 1，且恰在 $4\nmid N$ 时有严格优势。量子上界与已知加权奇环 XOR 定理的关系见说明。 |
| [Boyles · 有界零空间方盘的统一准多项式](problems/GridScaling/) · [ZIP](packages/GridScaling.zip?raw=1) | Boyles 的方盘数据在固定零空间维数时出现二次式。最坏按键数能用怎样的公式统一描述？ [原文](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L432-L457) | 对每个维数上界，一张有限的边长余数表同时描述全部符合条件的方盘。每个余数类从共同阈值起有精确二次式。已证明所有八维方盘甚至不能共用一个实多项式，两个无穷族的增长率是 $3/5$ 和 $161/289$。 |
| [Boyles · 四维零空间的方盘](problems/GridClicks/) · [ZIP](packages/GridClicks.zip?raw=1) | 当零作用按键空间恰为四维时，Boyles 数据中的最坏按键数公式是否总成立？ [原文](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L432-L457) | 所有这样的边长均可写成 $n=5q-1$，其中 $q$ 为奇数。最坏可解灯态恰需 $17q^2-10q$ 次按键，并可显式构造。 |
| [Boyles · 所有六维方盘的最坏按键数](problems/SixClicks/) · [ZIP](packages/SixClicks.zip?raw=1) | 零作用按键空间恰为六维时，Boyles 根据六个数据点提出的最坏按键数公式是否对所有边长都成立？ [原文](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/conjectures/conjectures.tex#L432-L451) | 若方盘零空间为六维，则 $n=12q-1$，最难灯态恰需 $88q^2-24q+1$ 次。构造的灯态全部 64 种解都有相同重量，覆盖整个 $n=12\cdot3^k-1$ 无穷族。 |
| [Savadatti–Zhang · 两比特满支撑符号的平均谱偏度](problems/PauliSkew/) · [ZIP](packages/PauliSkew.zip?raw=1) | 两比特满支撑 Pauli 符号图的平均谱偏度能否超过 Clifford 基准？ [原文](https://arxiv.org/html/2611.27724v1#S7.SS3) | 对全部 $2^{225}$ 个 Pauli 符号图，平均谱偏度的绝对值至多 $58/(45\sqrt5)$，严格低于 Clifford 基准 $1/\sqrt3$。归一化使用原论文已证明的 Haar 矩公式。 |

## 一般问题的部分答案与已知定理的推广

| 成果 | 原问题 | 我们证明了什么 |
| --- | --- | --- |
| [Busoni 等 · 稳定子 Rényi 熵的单侧优化](problems/OneSidedSchmidt/) · [ZIP](packages/OneSidedSchmidt.zip?raw=1) | 双侧局部酉优化的最低熵是否总由计算基 Schmidt 对齐态达到？ [原文](https://arxiv.org/html/2603.09155v2#S3) | 固定一侧的 Schmidt 基及标号后，另一侧所有局部酉中的最小值由计算基对齐态达到。适用于循环 Weyl 算符、所有局部维数和每个整数阶 $m\ge2$。论文的双侧问题仍开放。 |
| [Sierant · 非局域稳定子 Rényi-2 熵](problems/SierantGap/) · [ZIP](packages/SierantGap.zip?raw=1) | 计算基代表态与双侧局部酉优化所得二阶熵的差距能有多大？原文的 4 比特上界能否改进？ [原文](https://arxiv.org/html/2609.13106v2) | 计算基与任意局部酉最优值的差距上界由 4 比特降至 2 比特。Lean 从任意整数秩证明新组合界，并以原论文已证的矩阵迹关系推出熵界。 |
| [Liu、Low、Yin · 两比特二阶及以上的最大魔性](problems/MUBRealOrder/) · [ZIP](packages/MUBRealOrder.zip?raw=1) | Liu、Low、Yin 猜想的极值态在两比特、实数阶 $\alpha\ge2$ 时是否始终最优？ [原文](https://arxiv.org/pdf/2502.17550#page=4) | 以 Shen 等的二阶定理为前提，推出全部有限实数阶 $\alpha\ge2$ 的精确最大熵，并确定 480 个取等态。Lean 验证升阶推导与具体取等态，二阶界及其等号分类均引自原定理。 |
| [Savadatti–Zhang · 单比特量子门的正性收益](problems/DeficientQubit/) · [ZIP](packages/DeficientQubit.zip?raw=1) | 原文的单比特判据要求九个 Pauli 系数全非零。有系数为零时，Choi 正半定约束还能改善一阶认证斜率吗？ [原文](https://arxiv.org/html/2611.27724v1#S7.SS5) | 若九个 Pauli 相关系数中任一项为零，则加入 Choi 正半定约束不会改善一阶认证斜率。Lean 从实际复酉门证明次梯度证书，结合原论文定理 3 补全单比特判据。 |
| [Devriendt 与 Garcia · 2-sparse 图的电阻曲率](problems/SparseResistance/) · [ZIP](packages/SparseResistance.zip?raw=1) | 哪些双连通平面图允许所有顶点的电阻曲率非负？两侧大小相差一的二部图又有什么限制？ [原文](https://link.springer.com/article/10.1007/s00026-025-00774-x) | 当每条边至少有一个度数至多 2 的端点时，允许全顶点非负电阻曲率的连通图恰为路径、环和 $K_{2,3}$。Lean 验证生成树刻画下的无桥分类，其余情形引用原文命题 3.7。 |
| [Antis 等 · 十二元和积问题](problems/TwelveIntegerSets/) · [ZIP](packages/TwelveIntegerSets.zip?raw=1) | 每个十二元正整数集是否至少产生 41 个不同的两两和，或至少 41 个不同的两两积？ [原文](https://alexricemath.com/wp-content/uploads/2026/03/SP2025paperV3.pdf#page=12) | 十二元正有理数集若至多产生 41 个两两和，任意正有理几何级数最多包含其中 6 点，且能取等。十一元极值构型在两种基数均不超过 41 时的十二元扩展也唯一。原猜想 $SP(12)=41$ 的整体下界仍待证明。 |
| [Inoue–Inazu · 后缀减法游戏的语言类别](problems/VisiblyPushdownSubtraction/) · [ZIP](packages/VisiblyPushdownSubtraction.zip?raw=1) | 有哪些含非正则语言的上下文无关语言子类，能保证删除合法后缀后的游戏败态语言仍然上下文无关？ [原文](https://arxiv.org/html/2611.09157v1#S4) | 对问题 4.1，若允许删除的后缀构成可见下推语言，则必胜词与必败词也都是同一可见字母分类下的可见下推语言。Lean 从实际游戏构造识别这两个语言的 MSO 句子。 |
| [Alofi–Dukes · 随机沙堆的缺额多项式](problems/SandpileK3n/) · [ZIP](packages/SandpileK3n.zip?raw=1) | 一般完全二部图的随机常返配置按总缺额计数，所得系数是否总对数凹、单峰？ [原文](https://doi.org/10.1016/j.disc.2024.114323) | 对所有 $K_{3,n}$ 和任意吸收点，证明常返配置按总缺额计数的系数对数凹且单峰，并给出两种吸收点位置各自的计数公式。 |
| [Fazekas 等 · 二元词中的 Abel 平方](problems/FMMSFourLetterMinimum/) · [ZIP](packages/FMMSFourLetterMinimum.zip?raw=1) | 给定两种字母各自出现的次数，一个二元词至少包含多少种不同的 Abel 平方因子？ [原文](https://arxiv.org/html/2604.23188v1#S6) | 含四个 $a$ 和 $B\ge4$ 个 $b$ 时，不同 Abel 平方因子的最小数恰是 $1+\lfloor(B+2)/4\rfloor$。取等构造来自原文，此处证明任意排列的下界。 |
| [Cao 等 · 图奇偶网络的完美消去序](problems/Multipartite/) · [ZIP](packages/Multipartite.zip?raw=1) | 为使图具有完美消去序，至少需添几个全邻接顶点？若只在原顶点之间补边，又至少要补几条？ [原文](https://arxiv.org/abs/2509.10070) | 若有至少两个部，记第二大部的大小为 $b$，最大两部以外共有 $r$ 个顶点，则最少补点数与最少补边数均为 $\max(0,b-1-r)$。单部图已经有完美消去序。 |
| [Dębski 等 · 无限贪心 Barrycade 的遗漏数](problems/GreedyBarrycade/) · [ZIP](packages/GreedyBarrycade.zip?raw=1) | 在无限贪心填表中，除首行外，每行是否都恰好遗漏一个正整数？ [原文](https://arxiv.org/html/2609.18476v2#S3.SS1) | 第 $r$ 行（$r\ge2$）遗漏 1 到 $r-1$ 个数。若从第四行起各行都遗漏首项减一，则每个非首行恰好遗漏一个。一般情形的唯一性仍待证明。 |

## 整数数列中的猜想与勘误

| 成果 | 原问题 | 我们证明了什么 |
| --- | --- | --- |
| [A005558–A005562 · 象限随机游走](problems/A005562/) · [ZIP](packages/A005562.zip?raw=1) | Mathar 为象限游走的五个固定终点高度提出的计数递推，是否都成立？ [条目](https://oeis.org/A005558) | 从四方向步的定义证明任意终点高度的二阶递推，同时覆盖五个已提出的固定高度公式。 |
| [A245690 · 素因子筛的取值与首次位置](problems/A245690/) · [ZIP](packages/A245690.zip?raw=1) | 每个大于 2 的取值，其首次出现的下标是否都是素数连乘积，并且整除这个值的全部出现下标？ [条目](https://oeis.org/A245690) | 每个正整数值都在一条无穷等差数列上出现。记 P 为所有不超过 233 的素数之积。余数 6 首次出现在位置 7 × P，所有出现位置的最大公因数恰为 P。 |
| [A113572 · 按位置限制数位的倍数](problems/A113572/) · [ZIP](packages/A113572.zip?raw=1) | 首位为 1、后续数位按位置限制为素数或合数数字的 $n$ 位整数，若还要求被 $n$ 整除，是否只有在预期的下标才不存在？ [条目](https://oeis.org/A113572) | 恰在 $n$ 是 5 的倍数且 $n\ne5$ 时不存在。另证当 $k\ge m-1$ 时，$k$ 位 0、1 数字串能覆盖模 $m$ 的全部余数，当且仅当 $5\nmid m$。 |
| [A086004 · 十进制旋转加法](problems/A086004/) · [ZIP](packages/A086004.zip?raw=1) | 从素数出发，反复把十进制左右两半交换后与原数相加，最多能连续几次仍得到素数？ [条目](https://oeis.org/A086004) | 证明连续保持素性的最大次数恰为 4，四次实例中每一步的数值和素性均通过内核检查。 |
| [A001122 · 形如 $2^k+3$ 的素数](problems/A001122/) · [ZIP](packages/A001122.zip?raw=1) | 当 $k\ne2$ 且 $p=2^k+3$ 为素数时，2 是否总是模 $p$ 的原根？ [条目](https://oeis.org/A001122) | $2^{2191}+3$ 为素数，但 2 的乘法阶严格小于 $p-1$。 |
| [A347225 · 孪生素数的循环节](problems/A347225/) · [ZIP](packages/A347225.zip?raw=1) | 除周期差 1、2 外，每一种十进制循环节长度差是否最多只出现于两对孪生素数？ [条目](https://oeis.org/A347225) | 三对小于 6300 万的孪生素数具有相同正周期增量 1,120,174，落在原报告检验过的范围内。 |
| [A024399 · 基本对称函数之比](problems/A024399/) · [ZIP](packages/A024399.zip?raw=1) | 基本对称函数之比取整所得的数列，是否满足 Mathar 给出的七阶递推？ [条目](https://oeis.org/A024399) | 对所有下标证明七阶递推和生成函数的系数恒等式。 |
| [A121285 · 对称凸 permutomino 的枚举](problems/A121285/) · [ZIP](packages/A121285.zip?raw=1) | 按尺寸计数的对角对称凸 permutomino 是否满足 Mathar 的四项递推？ [条目](https://oeis.org/A121285) | 从已知组合计数闭式证明 Mathar 的四项递推，覆盖所有 $n\ge3$。 |
| [A004613 · 平方三元组的解数](problems/A004613/) · [ZIP](packages/A004613.zip?raw=1) | 固定 $n$，使 $n^2+m^2+1$ 为平方数的整数 $m\le n$，解数是否只能为零或至少两个？ [条目](https://github.com/oeis/oeisdata/blob/57bbd254e161585873f56950ff19ba6dc4aeb66c/seq/A004/A004613.seq#L14) | 两种读法都有唯一解的反例。要求 $m\ge0$ 时，$n=8$ 只有 $m=4$。允许负数时，$n=4$ 只有 $m=-8$。 |
| [A088226 · 最近平方数的下标勘误](problems/A088226/) · [ZIP](packages/A088226.zip?raw=1) | 按条目从 1 开始的下标，$2a(n)$ 是否等于 $n$ 到最近同奇偶平方数的距离？ [条目](https://oeis.org/A088226) | 每个正平方数加 1 都是反例。将距离公式中的 $n$ 换成 $n-1$，即对全部 $n\ge1$ 成立。 |

## 已有数学证明的 Lean 复验

| 成果 | 原问题 | 我们证明了什么 |
| --- | --- | --- |
| [Boyles · 方盘零空间维数的稳定性](problems/LightsGrid/) · [ZIP](packages/LightsGrid.zip?raw=1) | 沿奇数幂生成的方盘边长，零作用按键空间的维数是否最终稳定？稳定能出现多晚？ [原文](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/multiprime_stabilization/multiprime_stabilization.tex) | 在 Lean 中复验作者已公开的结果，包括奇数底数最终稳定、底数 57 的完整序列和任意晚稳定的构造。作者仓库的在先证明含标注为 AI 生成的文稿。 |

各证明包的 README 列出独立复验命令、所用文献及外部定理。Lean 主定理的公理依赖可用 `#print axioms` 查看。
