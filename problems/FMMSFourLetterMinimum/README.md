# 二元词中恰有四个 a 时，Abel 平方因子的精确最小数

设 $w$ 是一个有限线性二元词，含四个 $a$ 和 $B\ge 4$ 个 $b$。若一个非空连续因子可写作 $uv$，其中 $u,v$ 的长度相同，且每个字母在两半中的次数都相同，就称其为 Abel 平方。记 $\Theta(w)$ 为这样的**不同因子词**的个数。同一个字符串在多个位置出现只计一次。

本文件证明

$$
\min_{|w|_a=4,\ |w|_b=B}\Theta(w)
=1+\left\lfloor\frac{B+2}{4}\right\rfloor
\qquad(B\ge4).
$$

例如 $B=14$ 时最小值为 5。词 $ab^9a^3b^5$ 恰好含有 $aa,b^2,b^4,b^6,b^8$ 这五个 Abel 平方。若 $B\equiv2,3\pmod4$，这一结果比一般猜想给出的 $\lfloor |w|/4\rfloor$ 高 1。

## 原问题与在先结果

Szilárd Zsolt Fazekas、Adam Mammoliti、Robert Mercaş 和 Jamie Simpson 在 2026 年 4 月的预印本 *Binary Words Containing Few Abelian Squares* 中求出了一个字母出现 0、1、2、3 次时的极小值，并在第 6 节提出求其余字母次数的极小值。第 5 节定理 10、12 已给出每组字母次数下的候选极值词及其精确计数。上式补上了四个 $a$ 时对**任意排列**的下界。交换字母即得四个 $b$ 的对应结论。[原论文摘要及版本](https://arxiv.org/abs/2604.23188v1) · [第 5 节构造与定理 12](https://arxiv.org/html/2604.23188v1#S5) · [第 6 节研究问题](https://arxiv.org/html/2604.23188v1#S6)

本文的命题依据摘要、第 5 节定理 12 和第 6 节的固定字母次数问题。原稿第 13 猜想的印刷公式令两个有效分拆共用第二坐标 $k$，并用第一坐标写出下界，与任意 $B$ 的上述极小值问题表述有异。本结论的适用域为 $(4,B)$，一般次数与原稿第 13 猜想的全部参数仍需另证。[原稿第 5–6 节](https://arxiv.org/html/2604.23188v1#S5)

## 下界

将词唯一写成

$$
b^{r_0}a b^{r_1}a b^{r_2}a b^{r_3}a b^{r_4},
\quad r_i\ge 0,\quad B=\sum_{i=0}^4r_i.
$$

1. 令 $M=\max r_i$。最长的 $b$ 段包含 $b^2,b^4,\ldots,b^{2\lfloor M/2\rfloor}$，给出第一组不同因子。

2. 考察相邻的两个 $a$，令它们之间有 $g$ 个 $b$，左右相邻的 $b$ 段长度为 $L,R$。含这两个 $a$ 的候选因子形如 $b^x a b^g a b^z$。若 $g=u+v$ 且 $x+u=v+z$，则在内部 $b$ 段的第 $u$ 个字母后切开，得到相同长度和相同字母数的两半。令

   $$
   D=\min(L+R,2L+g,2R+g),\qquad
   K(L,g,R)=\left\lfloor\frac{D+2-(g\bmod2)}{2}\right\rfloor.
   $$

   对每个 $0\le i<K$，取 $s=2i+(g\bmod2)$，$t=(s+g)/2$，$x=\max(0,s-R,t-g)$，$z=s-x$，$u=t-x$，$v=g-u$。这些整数满足 $0\le x\le L$、$0\le z\le R$ 和上述切分条件。不同 $i$ 给出不同长度，不同内部间隙 $g$ 给出不同因子词。此构造在 `endpoints` 和 `pair_bound` 中实现。

3. 令 $H$ 为三个相邻对的 $K$ 中最大者。恒有

   $$
   \left\lfloor\frac{B+2}{4}\right\rfloor\le \lfloor M/2\rfloor+H.
   $$

   这个整数不等式的有限分类与 $B$ 的大小无关。每个三段组由 $K\le H$ 推出 $L+R+1$、$2L+g+1$、$2R+g+1$ 至少有一个不超过 $2H+(g\bmod2)$。任选三个三段组各自满足的一项，加上五个 $r_i\le M$，即可推出不等式。`capacity_cases` 和 `basic` 逐一验证这 $3^3$ 种线性约束组合。

4. 还要补上 1。若存在整个四个 $a$ 都出现的平方因子，它与前两组按 $a$ 的个数区分。若有两种不同的内部间隙都能产生二 $a$ 平方，则在一个最大族外至少还有一个二 $a$ 因子。余下情形中，三个间隙族只要非空就具有相同的内部间隙，同时不存在四 $a$ 平方。这时已有 $\lfloor M/2\rfloor+H\ge 1+\lfloor(B+2)/4\rfloor$。`exceptional` 证明这一加强式。

   具体地，当 $r_1=r_3$ 时，只要 $r_2$ 为偶数或有一端的 $b$ 段非空，便能取 $x,z\in\{0,1\}$ 并平分或近似平分 $r_2$，构造四 $a$ 平方。于是余下情形有 $r_0=r_4=0$、$r_2$ 为奇数，此时中间那一对的 $K$ 已够用。当 $r_1\ne r_3$ 时，首、末间隙族至少有一个为空。反向阅读后可设首族为空；由 $K=0$ 推出 $r_0=r_2=0$ 且 $r_1$ 为奇数。若 $r_3=0$，缺少四 $a$ 平方意味着 $r_4<r_1$；若 $r_3>0$，中间零间隙族非空且与末间隙不同，故末族也为空，从而 $r_4=0$。这两种情况下所需不等式分别由最长段和中间间隙族给出。`disabled_left` 处理最后两种情形。

前述计数均注入真实的连续因子集合。Lean 主定理的参数是任意 `List Bool`。`decompose` 从字母计数导出五段表示，`squares` 先枚举后缀的全部前缀，再去重并检查两半的 Parikh 向量。

## 达到下界的词

取 $j=2\lfloor(B+2)/4\rfloor+1$ 及 $h=B-j$。由 $B\ge4$ 得 $0\le h<j$，且 $j$ 为奇数。原论文定理 12 的构造在此给出 $w=ab^ja^3b^h$。形式证明再次核对了此词的上界，未将原论文中的定理加入公理。[原定理 12](https://arxiv.org/html/2604.23188v1#S5)

令 $C(t)$ 表示长度 $t$ 的前缀中的 $a$ 数，则 $C(0)=0$，而 $t\ge1$ 时有 $C(t)=1+\min(3,\max(0,t-j-1))$。从位置 $i$ 开始、半长 $k>0$ 的平方必须满足 $C(i+k)-C(i)=C(i+2k)-C(i+k)$。由 $j$ 为奇数、$h<j$ 和三个切点所在的前缀区间，或者两半都没有 $a$ 且 $2k\le j$，或者两半各有一个 $a$ 且 $k=1$。因此平方因子只能是 $aa$ 或 $b^{2k}$，其中 $1\le k\le\lfloor j/2\rfloor$。它们都实际出现，给出所求最小值。

## 公开论文和 AI 证明查重

检索日期为 2026 年 11 月 27 日（UTC+8）。核对标题和 arXiv 编号，还检索了 `abelian squares` 与 `four occurrences`、`exactly four`、`fixed Parikh vector`、`minimum`、`linear words` 的组合，以及极值词和四个同一字母的等价描述。所核对记录中未找到覆盖四次出现、任意 $B\ge4$ 的线性词精确极小值证明。公开索引覆盖不完整，检索结果无法证明全球首发。

- TrureTuring 的 #12378 直接研究同一预印本。记录按印刷版第 13 猜想的共用 $k$ 建立参数关系，验证了有限范围，给出循环词固定切点的障碍，并写明一般排列的下界仍未证明。#8589 的四字母反例 `abab` 针对第 4 猜想的取等条件。#29805 研究最大、非等价 Parikh 类数的渐近上界。[第 13 猜想的已有尝试](https://github.com/the-omega-institute/trureturing/issues/12378) · [第 4 猜想的反例](https://github.com/the-omega-institute/trureturing/issues/8589) · [不同的渐近计数问题](https://github.com/the-omega-institute/trureturing/issues/29805)
- `anaxia-research` 的形式化主定理处理循环词，其线性词部分报告了至长度 24 的计算。`farev/Matematica` 的公开记录报告了至长度 18 的计算。`chy4pro/automath` 将同一预印本列在待筛候选目录。[循环词定理与线性词检验](https://github.com/anaxia-research/literate-octo-lamp/blob/e3e0580c63fdfee8678b398fca0a12ade2956987/README.md) · [有界枚举记录](https://github.com/farev/Matematica/blob/4404f5bd46cd9248807980ea73a8a6467afdb342/log/2026-08-09-signed-difference-sets.md#L202-L229) · [自动选题目录](https://github.com/chy4pro/automath/blob/5542184180d014b68637851941109dd5e584e920/engine/briefs/archive_v4/E24_pool_triage_ccdm.md#L54-L61)
- GitHub 公共代码检索命中同源的反例、文献目录及循环词项目。等价英文检索还命中了 Fibonacci 词中的 antisquare 等不同命题。按论文编号查询的公开 Discussions 页面返回 0 条。[GitHub 代码检索](https://github.com/search?q=%222604.23188%22&type=code) · [等价描述检索](https://github.com/search?q=%22abelian+squares%22+%22four+occurrences%22&type=code) · [Discussions 检索](https://github.com/search?q=%222604.23188%22&type=discussions)
- EulerSolve 的公开论文目录内查询 `abelian square`、`Fazekas` 均无匹配。OpenAlex 的该预印本记录及其引用作品接口在核查时均显示 0 篇引用。[EulerSolve 目录](https://eulersolve.org/papers/) · [OpenAlex 来源记录](https://openalex.org/W7157343160) · [OpenAlex 引文接口](https://api.openalex.org/works?filter=cites:W7157343160)

## Lean 验证

本次验证使用 Lean 4.24.0 和 Mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。`four_letter_lower_bound` 给出全称下界，`four_letter_minimum` 用 `IsLeast` 同时给出下界和取等见证。两项 `#print axioms` 输出均只含 `propext`、`Classical.choice` 和 `Quot.sound`。源码未使用 `sorry` 或 `native_decide`。[Mathlib 固定版本](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.Finset.Card Mathlib.Data.List.Infix Mathlib.Order.Bounds.Defs
lake env lean -DwarningAsError=true FMMSFourLetterMinimum.lean
```
