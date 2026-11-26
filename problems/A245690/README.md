# A245690 的首次出现猜想在余数 6 处失效

OEIS A245690 的定义是这样的。给定 $n\ge3$，取不整除 $n$ 的最小素数 $p$，再取大于 $p$ 的最小正因子 $d\mid n$，令 $a(n)=d\bmod p$。K. Spage 猜想对每个 $x>2$，首次出现 $a(n)=x$ 的下标 $f(x)$ 都是素数连乘积，并且同一值的其余下标都被 $f(x)$ 整除。原记录为 $f(6)$ 预测了前 347 个素数的乘积。[OEIS 原文及数表](https://oeis.org/A245690) · [固定版本的猜想和预测](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A245/A245690.seq#L5-L21)

记 $r\#$ 为不超过 $r$ 的所有素数的乘积。由序列的原始定义可证

$$
\boxed{f(6)=7\cdot 233\#.}
$$

这个数含两个因子 $7$，因此不可能是素数连乘积。对每个 $t\ge0$，还有

$$
a(353\cdot337\#\cdot359^t)=6,\qquad
f(6)\nmid 353\cdot337\#\cdot359^t.
$$

这些下标严格递增，因而原猜想的后半句也有无穷多个反例。所有余数 6 的出现下标仍有一个能精确写出的最大公因数，恰为 $233\#$，比首次位置少一个因子 7。

另一个对整个数列成立的结论是，**每个正整数都会出现，而且对每个值，都有一条完整的等差数列上的下标取这个值**。因此原作者用到的首次出现位置 $f(x)$ 对每个正整数确实有定义。这个补充定理还允许把最小遗漏素数取到任意大。

## 为什么首次出现恰在这里

记 $P(p)=\prod_{q<p,\ q\text{ 为素数}}q$。只要 $p$ 是不整除 $n$ 的最小素数，就有 $P(p)\mid n$。若某对 $(p,d)$ 在任何下标出现，它自身的最小下标一定是 $L=\operatorname{lcm}(P(p),d)$。因为 $L\mid n$，$p$ 仍不整除 $L$，而且 $p$ 和 $d$ 之间不会有新的因子。另一方面 $d$ 和所有小于 $p$ 的素数都整除 $L$，故 $L$ 确实实现这对 $(p,d)$。

取 $N=7\cdot233\#$。其最小遗漏素数是 $239$。$240,242,243,244$ 分别含有 $2^4,11^2,3^5,2^2$，都不整除 $N$；$241$ 是遗漏的素数。$245=5\cdot7^2$ 整除 $N$，所以 $a(N)=245\bmod239=6$。

下面证明其最小性。若 $a(n)=6$，则 $p\ge7$。

- 对 $7\le p<239$ 的每个素数，下面表中有一项 $j\le5$ 使 $p+j\mid P(p)$。于是 $p<d\le p+5$，余数只可能为 $1$ 到 $5$。
- 对 $p=239$，有 $246=2\cdot3\cdot41\mid P(239)$，故 $d\le246$。唯一余数为 $6$ 的候选是 $245$。这迫使 $\operatorname{lcm}(P(239),245)=N\mid n$。
- 对 $p>239$，$n$ 连素数 $239$ 也必须包含，故 $n\ge239\cdot233\#>N$。

| $j$ | 满足 $p+j\mid P(p)$ 的素数 $p$，各取一个证书 |
|---:|---|
| 1 | 13, 29, 37, 41, 61, 73, 101, 109, 113, 137, 157, 173, 181, 193, 229 |
| 2 | 19, 31, 53, 67, 83, 89, 103, 127, 131, 139, 163, 199, 211, 233 |
| 3 | 7, 11, 23, 43, 59, 71, 79, 107, 151, 167, 179, 191, 223, 227 |
| 4 | 17, 47, 197 |
| 5 | 97, 149 |

Lean 由素性与整除关系直接重算这 48 个素数所需的证书。任意大的 $p$ 已由第三种情形统一覆盖。

## 后续下标与余数 4 的筛选条件

在 $M=353\cdot337\#$ 处，最小遗漏素数为 $347$，其后最小因子为 $353$。其中 $348,350,351,352$ 含有缺失的额外素因子幂，$349$ 是不整除 $M$ 的素数。因此 $a(M)=6$。对任意素数 $r>d$，把下标乘以 $r^t$ 将保留原有的 $p$ 和 $d$，因为直到 $d$ 的每一个正整数都与 $r$ 互素。取 $r=359$，即得开头的无穷族。该族各数的 $7$ 恰好出现一次，$N$ 则被 $49$ 整除。

上述 48 个小素数的排除证明还说明，每个余数 6 的下标都被 $233\#$ 整除。另一方面，两个已构造的出现位置 $N,M$ 满足 $\gcd(N,M)=233\#$。因此正整数 $g$ 整除全部出现位置的充要条件是 $g\mid233\#$。`common_divisors_of_six` 直接验证这个全称命题。

同一条目的附带猜想还要求，凡 $a(30030k)=4$ 均有 $17\nmid k$ 且 $19\nmid k$。取 $n=43\#=13082761331670030$。此时 $p=47$，$48,49,50$ 均不整除 $n$，$51=3\cdot17$ 整除 $n$，从而 $a(n)=4$。但 $k=n/30030$ 同时被 $17$ 和 $19$ 整除。[原文的必要条件](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A245/A245690.seq#L6)

## 哪些值会出现

固定目标 $x\ge1$。对每个 $1\le j<x$，各选一个不同的素数 $q_j>x$，施加同余条件 $p\equiv-j\pmod{q_j^2}$。模数两两互素，且 $0<j<q_j$，故中国剩余定理给出的剩余类与总模数互素。由狄利克雷算术级数素数定理，这个剩余类中有任意大的素数 $p>x$。取

$$n=P(p)(p+x),\qquad P(p)=\prod_{\ell<p,\ \ell\text{ 为素数}}\ell.$$

所有小于 $p$ 的素数都整除 $n$，而 $p$ 本身不整除 $n$。数 $p+x$ 是 $n$ 的因子。对任一中间数 $p+j$，其因子 $q_j^2$ 无法整除 $n$。这是因为 $P(p)$ 的素因子只出现一次，且 $q_j$ 若同时整除 $p+j$ 和 $p+x$ 就会整除 $0<x-j<q_j$。因此大于 $p$ 的首个因子恰为 $d=p+x$，余数就是 $x$。另一方面，余数为零将推出 $p\mid d\mid n$，与 $p$ 的定义矛盾。

一旦某个 $n$ 实现了这对 $(p,d)$，把 $n$ 改成 $n+t\,d!$（$t\ge0$），所有不超过 $d$ 的正整数的整除判断都保持相同。于是这条完整的等差数列有同一个取值 $x$。这里用到的算术级数素数定理和中国剩余定理均已有 mathlib 证明。[狄利克雷定理的库实现](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/NumberTheory/LSeries/PrimesInAP.lean) · [中国剩余定理的库实现](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Data/Nat/ChineseRemainder.lean)

## 任意取值的公共因子

更一般地，任给正整数 $x$ 和起点 $B$，如果正整数 $g$ 整除所有满足 $n>B$ 且 $a(n)=x$ 的下标，那么 **$g$ 一定没有平方素因子**。这解释了为什么首次位置中多出的第二个因子 7 不可能在所有后续位置保留。

为说明这一点，任取素数 $\ell$。在前面选 $p$ 的构造中，把各 $q_j$ 取到比额外的模数 $\ell^2$ 还大，就可以同时指定 $p$ 模 $\ell^2$ 所在的任意可逆剩余类。在 $1$ 与 $1+\ell$ 中选 $a$ 使 $\ell^2\nmid a+x$。这两个数都与 $\ell$ 互素，且它们的差 $\ell$ 不被 $\ell^2$ 整除，所以至少有一个合适。取 $p\equiv a\pmod{\ell^2}$，并取同一对 $(p,p+x)$ 的最小实现位置 $L=\operatorname{lcm}(P(p),p+x)$。由于 $\ell^2$ 既不整除 $P(p)$ 也不整除 $p+x$，它也不整除 $L$。又可选 $p>B$，从而 $L>B$。因此每个候选的平方素因子都会在任意晚的某个取值 $x$ 的下标上失效。

## Lean 复验

[A245690.lean](A245690.lean) 适用于 Lean 4.24.0 和 mathlib v4.24.0。主要定理为 `minimal_index_for_pair`、`first_six`、`first_six_not_primorial`、`later_sixes` 和 `four_filter_counterexample`。其中 `Witness` 直接要求 $p,d$ 的最小性，`value_unique` 验证余数由此唯一确定。整数余数、有限素数范围和最小公倍数都使用内核可归约的 `decide` 验证。运行命令如下。

```sh
lake exe cache get Mathlib.Data.Nat.Prime.Basic Mathlib.Data.Nat.GCD.Basic Mathlib.Tactic.NormNum
lake env lean -DwarningAsError=true A245690.lean
```

取值范围与等差数列的证明放在 [A245690Range.lean](A245690Range.lean)，沿用主文件的 `Witness` 和 `HasValue` 定义。在解压后的同一目录执行

```sh
lake exe cache get Mathlib.NumberTheory.LSeries.PrimesInAP Mathlib.NumberTheory.PrimeCounting Mathlib.Data.Nat.ChineseRemainder Mathlib.Data.Nat.Squarefree Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum
lake build A245690
lake env lean -DwarningAsError=true A245690Range.lean
```

`gap_in_reduced_class` 可将遗漏素数置于任意指定的可逆剩余类。`every_positive_gap` 构造指定的首个因子差，`value_range_after` 证明删除任意有限前缀后的取值范围仍是全体正整数，`progression_for_each_value` 给出等差数列。`occurrence_avoiding_prime_square` 和 `common_divisor_squarefree` 证明每个固定平方素因子都能避开，以及任意公共因子的无平方性。各定理的公理审计只列出 `propext`、`Classical.choice` 和 `Quot.sound`。

## 公开证明与 AI 工作检索

2026 年 11 月 27 日按 A245690、A245689、首次遗漏素数、最小较大因子、$233\#,239,245,347$ 以及 $f(6)$ 的完整十进制值核查。

- TrureTuring 在 2026 年 9 月 10 日留下了直接相关的公开记录。作者核对了 $n\le100000$ 的余数 4 筛选条件，明确标为待解，并提到更强的首次出现猜想。其文字提出了按最小遗漏素数分组的方向。本说明的 $43\#$ 反例、$f(6)$ 的精确值和无穷族均未见于该记录。该项目的已解目录中也未检出本编号。[TrureTuring 原始工作笔记，第 420 行](https://github.com/the-omega-institute/trureturing/blob/7f4bfeee6e1af4507b6ed80a664dcd213969c82b/Library/Words/oeis2026triage0910.md#L420) · [已解目录](https://www.trureturing.org/conjectures.html?lang=en)
- GitHub 默认分支代码搜索检出了上述笔记、按定义计算的 PARI 实现及 OEIS 索引。按 $f(6)$ 完整十进制值检索无匹配。按编号查询公开 Issues 和 Discussions，均返回零项。[代码检索](https://github.com/search?q=A245690&type=code) · [既有 PARI 实现](https://github.com/gfis/OEIS-prog/blob/fb375daf77829667fb7d46a43f3856dbfc5e8702/prog/gp/a245/A245690.gp) · [Issues](https://github.com/search?q=%22A245690%22&type=issues) · [Discussions](https://github.com/search?q=%22A245690%22&type=discussions)
- EulerSolve 研究目录内检索了编号、primorial 和 least missing prime。OpenAlex 的精确编号检索返回零篇。arXiv 域名网页搜索及学术全文索引按编号和问题描述检索，命中的素数连乘积论文研究其他数列。此次直接访问 arXiv 检索接口遇到 TLS 连接失败，未取得官方接口计数。[EulerSolve 论文目录](https://eulersolve.org/papers/) · [OpenAlex 查询](https://api.openalex.org/works?search=%22A245690%22&per_page=5) · [arXiv 查询入口](https://arxiv.org/search/?query=A245690&searchtype=all) · [近似关键词命中的另一项研究](https://arxiv.org/abs/2302.02838)

在这些可检索的公开来源中，未找到给出相同证明或反例的记录。未公开、未被索引或以其他措辞发表的工作仍可能存在。

取值范围的补充结论另以 `A245690 Dirichlet`、`least nondividing prime`、`divisor gap`、`every positive integer`、`surjectivity` 及其组合检索了 GitHub 代码、公开 Issues、论文索引和网页。未定位到把上述等差数列结论用于本题的在先证明。用中国剩余定理构造连续的非平方自由数是已有的数论方法。[GitHub 代码检索](https://github.com/search?q=A245690+Dirichlet&type=code) · [De Koninck 等人关于连续整数的在先构造](https://www.jeanmariedekoninck.mat.ulaval.ca/fileadmin/Documents/Publications/2013_consecutive_integers_divisible_by_the_square_of_their_largest_prime_factors.pdf)

对公共因子结论也以题号结合 common divisor、gcd of indices、squarefree、primorial 等关键词检索公开网页、arXiv 与 GitHub，未找到针对本数列给出的同一定理。[GitHub 检索](https://github.com/search?q=%22A245690%22+squarefree&type=code) · [数列的原定义](https://oeis.org/A245690)
