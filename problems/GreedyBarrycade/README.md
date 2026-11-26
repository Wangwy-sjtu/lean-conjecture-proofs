# 贪心无限 Barrycade 每一行的遗漏数上界

Michał Dębski 等在《Finite and infinite barrycades》第 3.1 节给出一个无限表。每次填入本行尚未用过的最小正整数，同时要求得到的新前缀和从未出现在任何前行的完整序列中。他们的猜想 2(1) 断言，除第一行外，每一行都恰好遗漏一个正整数。原文列出前四行的无限模式，第二、三、四行依次遗漏 1、2、10。[原论文，第 3.1 节](https://arxiv.org/html/2609.18476v2#S3.SS1) · [OEIS A399907](https://oeis.org/A399907)

**本次证明的全行界。** 按论文从 1 数行，第 $r$ 行的永久遗漏集合 $H_r$ 有限，且 $|H_r|\le r-1$。同一个证明文件还给出，第 $r$ 行第 $n$ 个数 $a_r(n)$ 对所有足够大的 $n$ 满足 $a_r(n)\le n+2^r-2$。上述两个不等式都对任意行成立。猜想要求 $|H_r|=1$，这里仍缺少这一结论。

## 为何前面每一行最多解释一个遗漏

固定第 $r$ 行，从它永久遗漏的正整数中任取一个有限集合 $H$。每条行的项都是互异的正整数，于是给定常数 $D$，每条行从某一项起的所有值都大于 $D$。我们只涉及前 $r$ 条行，因此可以同时选取足够晚的位置，使第 $r$ 行的下一项大于 $\max H$，而此前各行足够远的相邻前缀和之差也大于 $\max H$。

设当前前缀和为 $s$，并取 $s$ 大到超过上述各行早期的所有前缀和。对每个 $h\in H$，$h$ 从未用过、又比实际选中的下一项小。按贪心规则，拒绝 $h$ 的唯一理由是 $s+h$ 已经出现在某条前行的前缀和中。一条前行的两个晚期前缀和相距大于 $\max H$，而任意两个 $s+h$ 相距小于 $\max H$。所以不同的 $h$ 必须由不同的前行解释，给出 $|H|\le r-1$。若永久遗漏无限多，取出 $r$ 个就会矛盾。

## 行内项值的上界

记 $T_j=j(j+1)/2$。先按行归纳证明存在常数 $B_r$ 使 $a_r(n)\le n+B_r$ 对所有 $n$ 成立。这将该行第 $j$ 个前缀和夹在 $T_j$ 和 $T_{j+B_r}$ 之间。下界来自 $j$ 个互异的正整数，后一个上界来自所用整数都位于 $[1,j+B_r]$。若当前已选 $n$ 项且和为 $s$，取 $T_j\le s<T_{j+1}$，则 $j\ge n$。长度约为 $n$ 的候选区间只涉及每条旧行有界多个前缀索引。把有限条旧行的阻挡数相加，再多留一个候选，就能同时保证合法选择存在并控制其大小。Lean 中用显式宽度完成归纳，覆盖到每行第一步。

只研究足够大的 $n$ 时，这个界可以缩小。假设前面第 $i$ 行从某处起有位移上界 $b_i$。固定的早期例外在 $n$ 足够大后都已落入 $[1,n+b_i]$。此时要阻挡 $[1,n+1+b_r]$ 中的候选，前行第 $q$ 个前缀和应介于 $s$ 与 $s+n+1+b_r$ 之间。由三角数界得到 $j+1-b_i\le q\le j+2$，故该行至多阻挡 $b_i+2$ 个候选。取 $b_1=0$ 以及 $b_r=\sum_{i<r}(b_i+2)=2^r-2$ 即可归纳。这个上界控制的是每个足够晚的实际条目，前面的线性上界控制的是整行永久遗漏数。

## 核验和先例

`GreedyBarrycade.lean` 直接递归构造每条行，把所有先前完整行的正长度前缀和纳入禁集，并验证每次均取合法最小值。`mem_entriesUsed`、`mass_eq_prefix_sum` 和 `mem_forbidden` 将程序状态连到通常的数列定义。核心定理为 `omissions_linear_bound` 和 `eventual_entry_upper_bound`。Lean 代码的行号和位置从 0 起，所以代码行号 `r` 对应上文第 $r+1$ 行。Lean 和 mathlib 4.24.0 以警告作为错误编译通过。审计公理只有 `propext`、`Classical.choice` 和 `Quot.sound`。

2026-11-27 的检索发现了两个相关的公开 AI 项目。Patel 的项目已验证第五行完整无限尾部。trureturing 的技术记录给出一个从有限状态认证无限尾部的判据，并报告依次处理了前 200 行，同时明确标记一般猜想仍开放。另有仅针对同一论文猜想 2(2) 印刷起始下标的反驳。检索原论文、后续有限 Barrycade 论文、GitHub 代码与讨论、数学论坛和公开 AI 记录时，未查到本文对任意行的线性遗漏数界或最终项值界。检索无法保证全球首证。[第五行形式化及核查](https://github.com/thatnealpatel/proofs/issues/96) · [前 200 行及明确未解范围](https://github.com/the-omega-institute/trureturing/issues/8494) · [印刷下标问题](https://www.trureturing.org/research/debski-barrycade-omitted-element-refutation/) · [有限情形的后续论文](https://arxiv.org/abs/2609.24373)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Intervals Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Order.Interval.Finset.Nat Mathlib.Data.Set.Finite.Lattice Mathlib.Data.Finset.Max Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true GreedyBarrycade.lean
```
