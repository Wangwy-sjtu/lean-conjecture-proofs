# 指定素数和合数位置的十进制倍数

Amarnath Murthy 在 2005 年定义了数列 A113572。若存在首位为 1 的 $n$ 位正整数被 $n$ 整除，且从左数起，第 $r>1$ 位在 $r$ 为素数时是素数数字，在 $r$ 为合数时是合数数字，就取最小的这种整数，否则取 0。他指出 $5$ 的倍数中除 $5$ 外都是零项，并记录了 $n<10000$ 的计算，猜想没有其他零项。商数列 A113573 重复了同一猜想。[A113572 原始条目](https://oeis.org/A113572) · [A113573](https://oeis.org/A113573)

**结论。** 对每个 $n\ge1$，$a(n)=0$ 当且仅当 $5\mid n$ 且 $n\ne5$。证明还给出一个与素数位置无关的结论。若 $m\ge1$ 且 $k\ge m-1$，把十进制的 $k$ 个位置各填 0 或 1，允许前导零，能覆盖模 $m$ 的所有余数，当且仅当 $5\nmid m$。在 $m=9$ 时至少需要 8 个位置，所以统一界 $m-1$ 不能对所有模数减少一位。

## 证明

设 $R_k$ 为由 $k$ 个十进制 0、1 能取得的模 $m$ 余数。奇数 $m$ 若不被 5 整除，乘以 10 是所有余数上的置换。记 $S=10R_k$，添一位后得到 $R_{k+1}=S\cup(S+1)$。如果非空的 $S$ 还没有覆盖所有余数，它必有一个元素的后继不在 $S$ 内，否则从其中任一元素连续加 1 就遍历了所有余数。因此从 $R_0=\{0\}$ 出发，至多 $m-1$ 步便能覆盖。

偶数情形写 $m=2j$，按模数作强归纳。给定目标 $t$，末位取 $b=t\bmod2$。欲使 $b+10y\equiv t\pmod{2j}$，只需 $5y\equiv\lfloor t/2\rfloor\pmod j$。因为 $5\nmid j$，系数 5 可逆。当 $k\ge2j-1$ 时，剩余 $k-1$ 位至少有 $j-1$ 位，归纳假设保证得到这个 $y$。若 $5\mid m$，末位只能是 0 或 1，故模 5 余 2 的目标无法覆盖。在模 9 下，数值等于数字和的余数，七位至多含七个 1，无法余 8。

回到原题。在素数位置填 2，在合数位置填 8，首位填 1，由此得到 $n$ 位基准数 $B$。除首位外，每个位置都可以独立加 0 或 1。素数位置得到 2 或 3，合数位置得到 8 或 9，全程没有进位。若 $5\nmid n$，上面的余数定理保证这 $n-1$ 个位置能补出 $-B\pmod n$，得到所需倍数。$n=5$ 时有 $12245$。其余 $5$ 的正倍数均为合数，末位必须是合数数字 $4,6,8,9$ 之一，无法被 5 整除。

## 形式化和检索范围

Lean 文件使用 `Nat.digits 10 x` 读取实际十进制展开，`term` 用 `Nat.find` 选择最小倍数。`term_eq_zero_iff` 证明零项分类。`binary_coverage_iff` 证明对任意模数和任意目标余数的覆盖定理，`modulus_nine_sharp` 验证模 9 的界。Lean 和 mathlib 均为 4.24.0，以 `-DwarningAsError=true` 成功编译为 `.olean`。四项公理审计的并集为 `propext`、`Classical.choice`、`Quot.sound`。

## 既有结果与公开 AI 证明核查

**与既有数学的关系。** 奇模数时使用的集合增长不等式 $|S+\{0,1\}|\geq\min(m,|S|+1)$ 是 I. Chowla 于 1937 年给出的剩余类加法定理的两元素特例，文中的连续加 1 给出了这一特例的直接证明。另外，Vicente Saavedra-Araya 的推论 5.5 已知，在 $\gcd(m,10)=1$ 时，固定数字集 $\{0,1\}$ 的十进制整数在各余数类中渐近均匀分布。该推论讨论不限位数的分布。这里另外处理与 10 不互素的偶模数，给出恰好 $k$ 位的显式充分界，随后把余数覆盖用于随位置变化的素数与合数数字规则。原题本身是一项初等数论猜想。[Chowla 原文](https://academic.oup.com/qjmath/article-abstract/os-8/1/99/1564861) · [Saavedra-Araya，推论 5.5](https://doi.org/10.1017/etds.2025.10256)

**逐项计算。** GitHub 全局代码检索命中了 Sean A. Irvine 的 Java 实现。它对每个输入单独枚举倍数并检查数位，搜寻失败时允许返回 0。商序列代码对结果除以 $n$。这些代码可复核个例，程序没有给出所有允许输入必定找到见证的理由。另以两个编号查 GitHub Issues、将代码检索限定为 Lean，并核对 DeepMind 的 358 个 OEIS 目录项，均未见本题的 Lean 证明。[Irvine 的 A113572 实现](https://github.com/archmageirvine/joeis/blob/18a7aeb71b9c17d6262be076b0a621cdcf6e76e4/src/irvine/oeis/a113/A113572.java) · [A113573 实现](https://github.com/archmageirvine/joeis/blob/18a7aeb71b9c17d6262be076b0a621cdcf6e76e4/src/irvine/oeis/a113/A113573.java) · [DeepMind 形式化目录](https://github.com/google-deepmind/formal-conjectures/tree/main/FormalConjectures/OEIS)

**AI 与论文检索。** 2026-11-27 核对了 Epoch 论文关联的 444 条数列元数据，以及 Goyal、Epstein 的 AI 辅助 OEIS 证明库。EulerSolve 论文索引以两个编号、作者和数位限制关键词查找均未命中。trureturing 当日公开索引的 45,152 条记录中也未检出两个编号，其精确查询端点均返回 404。以两个编号及 `restricted digits`、`prescribed digits`、`every residue class`、`two consecutive digits` 和素数或合数位置等表述检索 arXiv 与公开网页，找到了上述经典工具和数位分布文献，未定位到解决 Murthy 零项分类的在先公开证明。公开检索无法排除未收录或未发表的个人和 AI 证明。[OEIS Open 论文](https://arxiv.org/abs/2608.11941) · [Epoch 元数据](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/metadata/oeis/sequences.json) · [Goyal 证明库](https://github.com/dvgyl/oeis-proofs) · [Epstein 证明库](https://github.com/Eppie/oeis-proofs) · [EulerSolve 论文目录](https://eulersolve.org/papers/) · [trureturing 索引说明](https://www.trureturing.org/api/)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.ZMod.Basic Mathlib.Data.Nat.Digits.Defs Mathlib.Data.Nat.Prime.Basic Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true A113572.lean
```
