# 无限贪心 Barrycade 的每个非首行都有遗漏

Michał Dębski 等在《Finite and infinite barrycades》第 3.1 节给出一个无限表。每次填入本行尚未用过的最小正整数，同时要求得到的新前缀和从未出现在任何前行的完整序列中。他们的猜想 2(1) 断言，除第一行外，每一行都恰好遗漏一个正整数。原文列出前四行的无限模式，第二、三、四行依次遗漏 1、2、10。[原论文，第 3.1 节](https://arxiv.org/html/2609.18476v2#S3.SS1) · [OEIS A399907](https://oeis.org/A399907)

**本次证明的全行界。** 按论文从 1 数行，每个 $r\ge2$ 的永久遗漏集合 $H_r$ 都满足 $1\le |H_r|\le r-1$。因此 A399907 所取的最小遗漏整数对每个适用索引确实存在。证明还给出，第 $r$ 行第 $n$ 个数 $a_r(n)$ 对足够大的 $n$ 满足 $a_r(n)\le n+2^r-2$，该行的每一个前缀和距离其上方最近的三角数都有只依赖于行的数值上界。一般行是否恰好遗漏一个仍待解决。

## 为何前面每一行最多解释一个遗漏

固定第 $r$ 行，从它永久遗漏的正整数中任取一个有限集合 $H$。每条行的项都是互异的正整数，于是给定常数 $D$，每条行从某一项起的所有值都大于 $D$。我们只涉及前 $r$ 条行，因此可以同时选取足够晚的位置，使第 $r$ 行的下一项大于 $\max H$，而此前各行足够远的相邻前缀和之差也大于 $\max H$。

设当前前缀和为 $s$，并取 $s$ 大到超过上述各行早期的所有前缀和。对每个 $h\in H$，$h$ 从未用过、又比实际选中的下一项小。按贪心规则，拒绝 $h$ 的唯一理由是 $s+h$ 已经出现在某条前行的前缀和中。一条前行的两个晚期前缀和相距大于 $\max H$，而任意两个 $s+h$ 相距小于 $\max H$。所以不同的 $h$ 必须由不同的前行解释，给出 $|H|\le r-1$。若永久遗漏无限多，取出 $r$ 个就会矛盾。

## 行内项值的上界

记 $T_j=j(j+1)/2$。先按行归纳证明存在常数 $B_r$ 使 $a_r(n)\le n+B_r$ 对所有 $n$ 成立。这将该行第 $j$ 个前缀和夹在 $T_j$ 和 $T_{j+B_r}$ 之间。下界来自 $j$ 个互异的正整数，后一个上界来自所用整数都位于 $[1,j+B_r]$。若当前已选 $n$ 项且和为 $s$，取 $T_j\le s<T_{j+1}$，则 $j\ge n$。长度约为 $n$ 的候选区间只涉及每条旧行有界多个前缀索引。把有限条旧行的阻挡数相加，再多留一个候选，就能同时保证合法选择存在并控制其大小。Lean 中用显式宽度完成归纳，覆盖到每行第一步。

只研究足够大的 $n$ 时，这个界可以缩小。假设前面第 $i$ 行从某处起有位移上界 $b_i$。固定的早期例外在 $n$ 足够大后都已落入 $[1,n+b_i]$。此时要阻挡 $[1,n+1+b_r]$ 中的候选，前行第 $q$ 个前缀和应介于 $s$ 与 $s+n+1+b_r$ 之间。由三角数界得到 $j+1-b_i\le q\le j+2$，故该行至多阻挡 $b_i+2$ 个候选。取 $b_1=0$ 以及 $b_r=\sum_{i<r}(b_i+2)=2^r-2$ 即可归纳。这个上界控制的是每个足够晚的实际条目，前面的线性上界控制的是整行永久遗漏数。

## 为何非首行至少遗漏一个数

对行数归纳，证明所有前行的前缀和各自在某个三角数下方距离 $C$ 以内，其中 $C$ 可以对当前有限条前行统一选取。第一行恰是 $1,2,3,\ldots$，所以归纳从 $C=0$ 开始。以下称这些区间为 $[T_j-C,T_j]$。

反设当前非首行最终用到了每个正整数。选到 $n$ 项时记 $s$ 为前缀和、$p$ 为已用最大数。由前述项值界，$n\le p\le n+B$。当 $n$ 足够大，所有不超过 $B+C+1$ 的数都已用过。如果下一步跳过 $p+1$，那么 $p+1$ 和所有 $h\le p$ 的未用正整数都遭拒，故 $s+p+1$ 和 $s+h$ 都落进前行的三角数区间。它们相差至多 $n-C$，又都超过 $T_n$，因而落在同一区间。于是 $p+1-h\le C$。这表明 $1,\ldots,n-C$ 已全部出现。把其余至多 $C$ 项分别用 $n+B$ 控制，得到 $s\le T_n+C(C+B)$。

第一行已经占用所有正三角数，故 $s>T_n$。由刚得到的上界，当 $n$ 足够大，$s+p+1$ 严格落在 $T_{n+1}$ 与 $T_{n+2}-C$ 之间。因此它属于不了任何一个前行区间，与 $p+1$ 遭拒矛盾。可见晚期最大已用数每次至多增加 1，往后再也不能产生新的空位。反设全行用到每个正整数，则那时留下的有限个空位也终将全部填满，届时已用集正好为 $[1,p]$，前缀和便是第一行已占用的 $T_p$，再次矛盾。

由此取得一个永久遗漏 $h$。该行以后选入的数都大于 $h$，故对每个足够晚的前缀和 $s$，$s+h$ 一定属于某条前行的禁区。这使得 $s$ 位于某个三角数下方距离 $C+h$ 以内。把有限个早期前缀并入常数，就得到本行也满足归纳条件。这里控制的是前缀和与三角数的数值差，强化了前面关于三角数索引的粗界。

## 核验和先例

`GreedyBarrycade.lean` 直接递归构造每条行，把所有先前完整行的正长度前缀和纳入禁集，并验证每次均取合法最小值。`mem_entriesUsed`、`mass_eq_prefix_sum` 和 `mem_forbidden` 将程序状态连到通常的数列定义。核心定理为 `nonfirst_has_omission`、`omissions_linear_bound`、`partial_sums_below_triangles` 和 `eventual_entry_upper_bound`。Lean 代码的行号和位置从 0 起，所以代码行号 `r` 对应上文第 $r+1$ 行。Lean 和 mathlib 4.24.0 以警告作为错误编译通过。审计公理只有 `propext`、`Classical.choice` 和 `Quot.sound`。

2026-11-27 的检索发现了两个相关的公开 AI 项目。Patel 的项目已验证第五行完整无限尾部。trureturing 的技术记录给出一个从有限状态认证无限尾部的判据，并报告依次处理了前 200 行，同时明确标记一般猜想仍开放。另有仅针对同一论文猜想 2(2) 印刷起始下标的反驳。检索原论文、后续有限 Barrycade 论文、GitHub 代码与讨论、数学论坛和公开 AI 记录时，未查到本文对每条非首行的遗漏存在性、对任意行的线性遗漏数界、最终项值界或三角数距离界。检索无法保证全球首证。[第五行形式化及核查](https://github.com/thatnealpatel/proofs/issues/96) · [前 200 行及明确未解范围](https://github.com/the-omega-institute/trureturing/issues/8494) · [印刷下标问题](https://www.trureturing.org/research/debski-barrycade-omitted-element-refutation/) · [有限情形的后续论文](https://arxiv.org/abs/2609.24373)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Intervals Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Order.Interval.Finset.Nat Mathlib.Data.Set.Finite.Lattice Mathlib.Data.Finset.Max Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true GreedyBarrycade.lean
```

## 遗漏数确定前缀和对应的三角数

这份补充继续研究 Dębski 等的贪心无限表。对一个固定行，令 $S_n$ 为前 $n$ 项之和，$H$ 为永久遗漏的正整数集合，$d=|H|$，$T_k=k(k+1)/2$。每一行的 $H$ 已在基础文件中证明有限，非首行还已证明 $H$ 非空。[原论文猜想 2(1)](https://arxiv.org/html/2609.18476v2#S3.SS1)

**精确约束。** 对所有充分大的 $n$ 都有

$$
\max H\ \le\ T_{n+d}-S_n\ \le\ \sum_{h\in H}h,
$$

空集的最大值取 0。于是原猜想对单行等价于一个关于整个无限尾部的判据。设这一行恰遗漏 $a$，则从某个 $N$ 起恒有 $S_n=T_{n+1}-a$，第 $k$ 项恒为 $k+1$，这里 $k$ 从 1 计。反过来，一行只要最终满足 $a_r(k)=k+1$，就恰遗漏一个数。若有多项遗漏，上式仍然适用。它还给出各项与平移后位置的双侧有界偏差。一般行是否全部具有这个单位平移尾部仍待证明。

### 三角数的索引为何正好偏移 $d$

基础文件已知对每个 $n$ 可以选取 $w(n)$，使 $S_n\le T_{w(n)}\le S_n+c$。由 $S_n\ge T_n$ 得 $w(n)\ge n$。本行的项互异，所以充分晚时每项大于 $c$，这迫使 $w(n+1)>w(n)$。另一方面，下一项至多 $n+1+B$，而连续跨过两个三角数要增长至少 $2w(n)+3$；$n$ 足够大时不可能。因此 $w(n+1)=w(n)+1$，并有常数 $e$ 使 $w(n)=n+e$。相邻两式相减又给出第 $n+1$ 项与 $n+e+1$ 的差绝对值至多 $c$。

取固定的 $L$ 足够大。对充分大的 $t$，$H$ 中的所有数都不超过 $t$。在前 $t+L$ 项中，每个不超过 $t$ 且不属于 $H$ 的正整数都已出现，否则它将只能在更晚处出现，与刚得到的逐项下界冲突。因此其中恰有 $t-d$ 项来自 $[1,t]$，余下 $L+d$ 项均在 $t$ 与 $t+L+B$ 之间。这给出 $S_{t+L}+\sum H=T_t+(L+d)t+O(1)$。而 $S_{t+L}=T_{t+L+e}+O(1)=T_t+(L+e)t+O(1)$。比较一次项便知 $e=d$。

## 精确误差为何受遗漏值控制

把前 $n$ 个数与 $H$ 合在一起，会得到 $n+d$ 个互异正整数，故 $S_n+\sum H\ge T_{n+d}$。这一侧对所有 $n$ 已经成立。

若 $H$ 非空，取 $m=\max H$。充分晚时下一项大于 $m$，因此 $S_n+m$ 一定被某个先前行的前缀和挡住。由基础文件，先前有限条行的所有前缀和都处在某个三角数下方一个统一的固定距离内。若 $S_n+m>T_{n+d}$，下一可能的三角数至少是 $T_{n+d+1}$。但 $S_n\le T_{n+d}$，所以两数相距至少 $n+d+1-m$，随 $n$ 增长而发散，矛盾。这给出另一侧。当 $H=\{a\}$ 时上下界均等于 $a$。反向判据来自尾部覆盖全部大整数以及开头有限项的计数。

### 形式化与已有证书

`GreedyBarrycadeStructure.lean` 导入同一目录的 `GreedyBarrycade.lean`。`alignment_by_omission_count` 确定三角数索引偏移和项值的双侧偏差，`deficit_bounds` 证明上方精确不等式，`singleton_iff_tail` 证明单值遗漏的双向判据。Lean 和 mathlib 4.24.0 关闭警告容忍后编译通过，审计只列出 `propext`、`Classical.choice`、`Quot.sound`。

公开讨论给出了若干具体行最终稳定的充分证书，并报告验证前 200 行。这里的判断不限于事先找到证书的行，认定任何单值遗漏行都必然最终稳定，同时对任意多值遗漏行给出误差上下界。该结果作为猜想的等价形式和结构性部分进展。[已有前 200 行的计算证书](https://github.com/the-omega-institute/trureturing/issues/8494) · [已公开的第五行 Lean 证明](https://github.com/thatnealpatel/proofs/issues/96)

在本目录运行以下命令复验结构定理。

```sh
lake build GreedyBarrycade
lake env lean -DwarningAsError=true GreedyBarrycadeStructure.lean
```

## 任意有限组贪心行共享一个最终周期

沿用 Dębski 等论文第 3.1 节的贪心表。$a_i(n)$ 表示第 $i$ 行从 1 数起的第 $n$ 项，$S_i(n)$ 是前 $n$ 项之和，$d_i$ 是该行永久遗漏的正整数个数。它们都由原始贪心构造决定。[原论文](https://arxiv.org/html/2609.18476v2#S3.SS1)

**定理。** 对任意给定的有限行数 $R$，存在同一正整数 $P$ 和起点 $N$，使得前 $R$ 行在所有 $n\ge N$ 处都满足

$$
a_i(n+P)=a_i(n)+P,\qquad S_i(n+P)-S_i(n)=P(n+d_i)+\frac{P(P+1)}2.
$$

因此各行的位移 $a_i(n)-n$ 最终周期化。每一个完整晚期周期内的位移平均值恰好是实际遗漏数 $d_i$。这是一般猜想的部分进展。周期 $P$ 和起点 $N$ 可以依赖 $R$，定理没有给出 $P=1$ 或 $d_i=1$。

### 有限历史怎样决定无限构造的下一步

把各行的前缀按三角数对齐。在第 $i$ 行，前 $n$ 项对应第 $k=n+d_i$ 层，记 $D_i(k)=T_k-S_i(n)$。此前证明了对足够大的 $k$，$D_i(k)$ 是非负有界整数。固定有限条行后可以选取同一个上界 $W$。相邻层的差给出下一项

$$
a_i(n+1)=k+1+D_i(k)-D_i(k+1).
$$

因而实际被选的候选 $x$ 必在 $[k+1-W,k+1+W]$ 内。若 $x$ 已在本行出现，它在充分晚时只能出现在紧邻的前 $2W$ 层。比此更老的层产生的项都比 $x$ 小，各行中有限个早期例外也可以由同一个起点排除。知道这段历史的各层差额，即可由相邻两层的公式恢复已用过的候选。

若候选使新前缀和落入某条前行 $j$，该前行里的撞击只能发生在第 $k+1$ 层。因为所有差额都有统一数值界，而足够晚的相邻三角数之间的距离已远大于此界。碰撞的精确条件是

$$
x+D_j(k+1)=k+1+D_i(k).
$$

现在比较两处具有相同最近 $2W+1$ 层差额的历史。假设它们相距 $p$ 层，将候选 $x$ 平移为 $x+p$。根据以上两条判断，本行已用情况相同。先处理最低行，再逐行向上，每条前行已经确定的下一层差额也相同，因此前行碰撞条件相同。两处贪心选择都取最小合法值，这强迫所选值恰差 $p$，下一层所有差额再次相同。

最近 $2W+1$ 层的 $R$ 行差额向量只有有限种取值，因而其中一个向量必在两个足够晚的层重复。逐层应用上一段，重复从此持续，得到共同周期 $P$。此时在相距 $P$ 层的两个前缀和中差额抵消，三角数恒等式 $T_{k+P}-T_k=Pk+T_P$ 即给出定理的第二个等式。

### 形式核验与公开先例

`GreedyBarrycadePeriod.lean` 依次导入前两份 Lean 成果中的定义与定理。`common_period_and_block_sum` 同时证明周期和周期求和公式，`eventual_common_period` 单独给出项值周期。Lean 和 mathlib 4.24.0 以 `-DwarningAsError=true` 成功编译，公理审计仅为 `propext`、`Classical.choice`、`Quot.sound`。

公开的有限尾部证书已对前 200 行报告周期为 1 的特例，第五行另有公开 Lean 证明。按原论文题名、`eventually periodic`、`finite-state`、`common period`、`greedy quasi-barrycade` 检索原论文、OEIS、GitHub 讨论及公开 AI 记录，未定位到关于任意有限行组最终共同周期的先前证明。[前 200 行核查](https://github.com/the-omega-institute/trureturing/issues/8494) · [第五行独立证书](https://github.com/thatnealpatel/proofs/issues/96)

在本目录复验周期定理。

```sh
lake exe cache get Mathlib.Data.Fintype.Pigeonhole Mathlib.Data.Fintype.Pi
lake build GreedyBarrycadeStructure
lake env lean -DwarningAsError=true GreedyBarrycadePeriod.lean
```
