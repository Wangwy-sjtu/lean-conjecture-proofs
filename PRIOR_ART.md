# 公开证明核查记录

核查日期为 2026 年 11 月 27 日。下表逐项记录与当前结论最接近的公开结果。这里的“未检出”只说明检查过哪些来源。即便 Lean 完整验证了命题，仍有可能存在以不同术语发表、尚未索引或尚未公开的证明。

| 命题 | 已有公开材料 | 本仓库验证的范围 |
| --- | --- | --- |
| A245690 的首次出现位置及其整除性 | TrureTuring 在 2026 年 9 月明确记录了余数 4 的筛选条件在十万以内通过，仍将其标作待解，并提到关于首次出现位置的更强猜想。[先前 AI 笔记，第 420 行](https://github.com/the-omega-institute/trureturing/blob/7f4bfeee6e1af4507b6ed80a664dcd213969c82b/Library/Words/oeis2026triage0910.md#L420) | 求出余数 6 的精确首次出现位置，证明其后的整除性有无穷反例，并反驳余数 4 的筛选条件。 |
| A113572 的零项 | 作者报告检验至一万，jOEIS 已给出逐输入搜索。已有工作还包括固定数字集在与 10 互素模数下的渐近分布定理。[原猜想](https://oeis.org/A113572) · [Saavedra-Araya 推论 5.5](https://doi.org/10.1017/etds.2025.10256) | 证明奇偶模数下的有限位数覆盖，继而从数位位置规则证明零项恰为大于 5 的 5 的倍数。等价商序列 A113573 合并计入本题。 |
| A086004 的五次旋转加法 | Wu 给出了四次成功的例子和排除六次的证明。2023 年的计算记录仍将五次描述为待解决。[吴的原注释](https://oeis.org/A261458) · [计算记录](https://voodooguru23.blogspot.com/2023/01/rotate-and-add.html) | 对任意实际十进制位宽证明连续五次不可能。 |
| A001122 的第二项原根观察 | 指数 2191 在素数表中已有记录。AlphaProof Nexus 有一条提到 A001122 的已解命题，它的假设涉及另一数列 A091669 的整除性。Ordowski 同段第一项观察已有反例 643。[指数表](https://oeis.org/A057732) · [DeepMind 的确切命题](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/OEIS/91669.lean) · [原注释](https://oeis.org/A001122) | 给出 $2^{2191}+3$ 及其五次幂余数证书，反驳第二项观察。 |
| A024399 的七阶递推 | 分子闭式和使用七阶递推的 LODA 实现均已公开。[分子闭式](https://oeis.org/A024392) · [2025 年程序](https://github.com/loda-lang/loda-programs/blob/537ce9a79f9f/oeis/024/A024399.asm) | 从基本对称多项式及整除取整出发验证递推和生成函数系数。 |
| A347225 的循环节差 | 原注释报告十亿内未见反例。按三对素数、共同正差 1,120,174、作者以及十进制乘法阶检索，未检出同一反例或另一份推翻该上限的公开证明。[原注释](https://oeis.org/A347225) | 用三对六个小于 6300 万的素数反驳该上限，逐个认证素性与精确周期。 |
| A004613 的唯一性观察 | Choi 2016 年已列出相关平方三元组。GitHub 有些命中仅引用 A004613 用于两平方和的判别。[原论文](https://doi.org/10.1155/2016/5189057) · [2026 年提出的观察](https://github.com/oeis/oeisdata/blob/57bbd254e161585873f56950ff19ba6dc4aeb66c/seq/A004/A004613.seq#L14) | 验证固定坐标的全部解集，以旧三元组反驳后出的解数判断。 |
| A121285 的四项递推 | Disanto 与 Rinaldi 给出闭式和生成函数，jOEIS 已实现闭式。[原论文](https://dmtcs.episciences.org/articles/3638/download) · [jOEIS](https://github.com/archmageirvine/joeis/blob/master/src/irvine/oeis/a121/A121285.java) | 以已发表的闭式为起点，证明 Mathar 后来写下的递推。 |
| A088226 的下标勘误 | OEIS 同页有等价分块公式与零基程序。另一公开项目把 A088226 列入候选清单并保存了原条目。该项目的证明目录中未检出这道题的解答。[作者程序](https://github.com/oeis/oeisdata/blob/75e849f306e5850b3ea1a26e65577cd9dbcb2dc6/seq/A088/A088226.seq#L5-L10) · [候选清单](https://github.com/joaquimmj/oeis-conjectures/blob/71d80d2caef1/conjectures/crawl/old_targets.json) | 从原递推证明修正公式，给出原文字面命题的无穷反例。此项属于勘误。 |

## 核查过的公开 AI 记录

逐一核对了 Epoch AI 的 492 条正式猜想元数据及其运行结果索引，并搜索了 DeepMind Formal Conjectures 和 Epoch 求解框架的公开源码。上表各题号均未作为这 492 条中的主问题出现。不同编号的引用也会命中，例如表中所列的 A091669。[Epoch 的 492 条命题](https://github.com/epoch-research/LeanOpenProblems-results/blob/cbb7cb657f24157d9ebb7640ec50bd35bad78ad8/metadata/oeis/conjectures.json) · [Epoch 论文](https://arxiv.org/abs/2608.11941) · [DeepMind 论文](https://arxiv.org/abs/2605.22763)

在十个公开代码快照中，按编号、部分等价表述、具体指数和素数反例检索了 Lean、论文源码、说明和数据文件。数据镜像、旧选题清单、序列计算程序与正式证明单独核对。另以 GitHub Code 和 Issues 扩大检索，并检查 TrureTuring 的四份公开分流报告，以及 arXiv 可索引的论文及引用。arXiv 的精确题号 API 本轮连接失败，论文核对采用网页索引和可打开的论文原页。[Eppie](https://github.com/Eppie/oeis-proofs) · [dvgyl](https://github.com/dvgyl/oeis-proofs) · [joaquimmj](https://github.com/joaquimmj/oeis-conjectures) · [VictorLiwentao](https://github.com/VictorLiwentao/lean-oeis-proofs) · [otoi-lab](https://github.com/otoi-lab/oeis-lean-proofs) · [vishal1383](https://github.com/vishal1383/lean-conjectures) · [mariyaholic](https://github.com/mariyaholic/lean-fc-proofs) · [IvanGrigin](https://github.com/IvanGrigin/oeis-short-proofs) · [TrureTuring](https://github.com/the-omega-institute/trureturing/tree/dev/Library/Words)

例如，筛选 A394576 时找到了同题的公开预印本和 Lean 工作，因此该题未收入成果。另一个被筛掉的方向是四元素 Sidon 集在 Singer 构造中的不可扩展性。作者的 arXiv 撤稿说明指向此前已在 MathOverflow 公开的更强结果。[A394576 的在先工作](https://github.com/dvgyl/oeis-proofs/tree/931b76616e14/preprints/A394576-A-greedy-sequence-avoiding-sums-of-three-consecutive-terms) · [arXiv 撤稿说明](https://arxiv.org/abs/2604.25214) · [MathOverflow 原证明](https://mathoverflow.net/a/503157)
