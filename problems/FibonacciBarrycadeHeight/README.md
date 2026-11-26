# 斐波那契数列 barrycade 的精确最大高度

Dębski、Grytczuk、Naroski、Pawlik、Przybyło 和 Śleszyńska-Nowak 在《Finite and infinite barrycades》第 4 节询问，给定递增正整数序列 $A$ 时，前 $n$ 项可组成的 barrycade 最大高度 $h_A(n)$ 怎样增长，并点名了素数和斐波那契数。本结果完整回答其中的斐波那契数情形。依照原文的递增正整数约定，取 $A=(1,2,3,5,8,13,\ldots)$。每一行是这 $n$ 个数的一个排列，不同行的非空真前缀和彼此不同。[原论文第 4 节末段](https://arxiv.org/html/2609.18476v2#S4)

**定理。** 对每个正整数 $n$，精确最大高度为

$$
h_A(n)=\begin{cases}n-1,&n\in\{3,4,5\},\\ n,&\text{其他正整数 }n.\end{cases}
$$

例如 $n=4$ 时可取 $(1,3,2,5)$、$(3,2,5,1)$、$(2,5,1,3)$。它们的三个真前缀和分别为 $1,4,6$、$3,5,10$ 和 $2,7,8$。九个数互异。若想加到四行，就需要十二个不同的真前缀和，而所有真前缀和都在 $1$ 到 $10$ 之间。

## 上界

当 $n\ge2$ 时，各行首项本身是真前缀和，必须两两不同，所以高度至多为 $n$。另记所有项之和为 $T$。每行提供 $n-1$ 个真前缀和，均落在 $[1,T-1]$，因此任何高度 $h$ 都满足 $h(n-1)\le T-1$。对 $n=3,4,5$，相应的 $T$ 分别为 $6,11,19$，从而上界分别降为 $2,3,4$。$n=1$ 时只有一个不同的排列。源码为 $1\le n\le8$ 逐一给出了达到上界的实际排列，并由 Lean 内核核对。

## 任意大阶的统一构造

采用从零开始的指标，令 $f_i=F_{i+2}$，其中 $F_0=0,F_1=1$。当 $n\ge9$ 时，取以下指标圆排列，删除所有不小于 $n$ 的指标。

$$
(4,0,2,6,8,10,\ldots;\quad 1,5,3,7,9,11,\ldots).
$$

把指标 $i$ 换成 $f_i$，分别从圆上每个位置开始顺时针读满一周，得到 $n$ 个排列。比如 $n=9$ 的圆是 $(8,1,3,21,55,2,13,5,34)$。每个非空真前缀对应这个圆上的一段连续弧。一段弧的指标集合可以由它的起点及长度唯一确定。因此只需证明，这个圆上两个不同的连续弧的斐波那契权重和总不相等。

## 为什么有限核验能覆盖任意阶

对两个待比较的弧，在第 $i$ 个指标放入两个成员位 $a_i,b_i\in\{0,1\}$，分别记录它是否在两条弧中。一个非空真圆弧的成员位沿圆周恰好变化两次。假如两个弧相撞，则

$$
\sum_{i=0}^{n-1}(a_i-b_i)F_{i+2}=0.
$$

扫描指标时，只需为斐波那契进位保留五种可能。若在第 $n$ 层的待传数为 $(u,v)$，它代表 $uF_{n+2}+vF_{n+1}$。向下一层处理数位 $d=a_i-b_i$ 时，利用斐波那契递推，进位更新为 $(u+v+d,u)$。所有更低位的绝对贡献严格小于相邻两个权重之和。由此可核验，能够参与总和为零的路径，其活跃进位都在 $(0,0),(1,0),(-1,0),(0,1),(0,-1)$ 之中。

圆周顺序由一个偶指标块和一个奇指标块拼成。每个块记录首尾的两个成员位，还需记录两个成员位在块内的变化总数、是否出现过不同的数位，以及下一项应追加到哪个块。某成员位的块内变化一旦超过两次，这两个候选就不能同时表示圆弧。末尾把两块首尾连接，即可得到两个成员位沿完整圆周的变化次数。

Lean 从六个固定低指标的所有成员位赋值出发，检查初始表、每个合法进位的转移、长度增加时的封闭性，以及最终是否可能出现反例。从长度 9 起使用一张含 296 条记录的闭合表。所有可能长度都由归纳纳入该表。表中凡是最终进位为零且两组圆周变化次数均不超过二的记录，两组成员位处处相同。代码随后把这一结论传回实际旋转排列和真前缀和。状态表本身可以重新生成，证明要求的各项覆盖与封闭条件都由 Lean 内核重新计算。

## 先例核查与复现

原文提出此问题时没有指定 $h_A(n)$ 的公式。Binięda 等的后续论文为连续整数砖长 $1,2,\ldots,n$ 给出接近最优的构造。公开 AI 项目中找到的同论文结果涉及贪心无限表所漏元素及早期行的证书。用题名、`Fibonacci barrycade`、`disjoint proper prefix sums`、`modular Golomb ruler with prescribed Fibonacci gaps`、`distinct cyclic interval sums` 等表述检查 arXiv、数学论坛、GitHub 代码、议题、提交与公开证明索引，目前未定位到这个指定斐波那契间距问题的全阶解。有限自动机处理斐波那契数制是已有方法，本题的具体贡献为圆排列、全阶无碰撞证明及精确高度公式。[连续整数的后续论文](https://arxiv.org/abs/2609.24373) · [已公开的贪心表证明](https://github.com/the-omega-institute/trureturing/issues/8494) · [Shallit 和 Shan 的斐波那契数制自动机方法](https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?AFL2023.18.pdf=)

三个文件依次导入。`FibonacciCircleAutomaton.lean` 给出进位与有限闭包，`FibonacciCircle.lean` 将其转换为实际排列的不相撞定理，`FibonacciBarrycadeHeight.lean` 按原文定义极值，并在 `fibonacci_barrycade_height` 证明所有正整数阶的结论。Lean 和 mathlib 版本均为 4.24.0。所有文件以 `-DwarningAsError=true` 通过，有限证书用 `decide +kernel` 计算，主定理的公理报告为 `propext`、`Classical.choice`、`Quot.sound`。

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.List.Perm.Subperm Mathlib.Data.Fintype.Pigeonhole Mathlib.Data.Fintype.Prod Mathlib.Data.List.Perm.Basic Mathlib.Algebra.BigOperators.Group.List.Lemmas Mathlib.Data.Nat.Fib.Basic Mathlib.Data.List.Rotate Mathlib.Tactic.Linarith
lake build FibonacciCircle
lake env lean -DwarningAsError=true FibonacciBarrycadeHeight.lean
```
