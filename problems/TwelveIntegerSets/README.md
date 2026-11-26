# 十二元和积问题中的几何级数交点上界

Antis、Britt、Chapman、Hawkins、Rice、Warren 在 2026 年论文第 6 节猜想，每个十二元正整数集至少给出 41 个不同的两两和或 41 个不同的两两积。两数可以相同。论文已经给出同时只有 41 个和、35 个积的例子。本次证明了一个对全部十二元集适用的必要条件，原猜想中的全局下界仍待证明。[原论文第 6 节](https://alexricemath.com/wp-content/uploads/2026/03/SP2025paperV3.pdf#page=12) · [arXiv 版本记录](https://arxiv.org/abs/2601.21828)

**定理。** 设 $A$ 是十二元正有理数集，$|A+A|\le 41$。任取正有理数 $c$ 和大于 1 的有理数 $r$，则

$$
\bigl|A\cap\{c,cr,cr^2,cr^3,\dots\}\bigr|\le 6.
$$

这个界取得到。作者的例子 $\{1,2,3,4,6,8,9,12,16,18,24,32\}$ 包含 $1,2,4,8,16,32$ 六个不同的二的幂。Lean 重新数出了 12 个元素、41 个和与 35 个积。集合中落在级数上的指数允许任意跳跃，其余元素只需为正。原论文的推论 6.2 已将小积集归入一维或二维乘法结构。本定理补充了小和集沿任一有理几何级数的浓度限制。[原论文推论 6.2](https://alexricemath.com/wp-content/uploads/2026/03/SP2025paperV3.pdf#page=13)

## 一般计数不等式

任取正有理数集中的 $t$ 个级数内点组成 $B$，再任取 $m$ 个级数外点组成 $T$。若 $B\cup T\subseteq A$，则

$$
2|A+A|\ \ge\ t(t+1)+2tm-m(m+3).
$$

证明分三步。

1. 写 $r=p/q>1$，其中 $p,q$ 互素。两组个数相同且每组最多有 $p$ 项的 $r$ 的非负整数次幂，如果和相等，指数多重集就相同。清分母后对 $p$ 取模，得到两边零次幂的个数模 $p$ 相等。可能相差 $p$ 的端点情形由 $r>1$ 排除。消去零次幂后除以 $r$，归纳即可。因此 $B$ 的无序两两和都不同，共有 $t(t+1)/2$ 个。
2. 每个级数外的 $x>0$ 所给出的平移 $x+B$ 至多有两个点落入 $B+B$。归一化为 $c=1$。当 $r\ne2$ 时，分子 $p\ge3$，两次碰撞会给出两组三项幂和相等，第一步迫使两个平移指数相同。当 $r=2$ 时，方程 $x+2^a=2^i+2^j$ 中单列 $a=v_2(x)$。其余解必须满足 $\min(i,j)=v_2(x)$。这是因为两侧取 2 进赋值后，如果较小指数为 $a$，则消去 $2^a$ 会迫使 $x$ 本身是二的幂。消去共同项后用两项和的唯一性，可知除单列指数外至多还有一个 $a$。
3. 不同外点给出的两个平移 $x+B,y+B$ 至多有一个公共点。否则相减得到 $B$ 中一组非平凡的两项和碰撞。把所有平移逐个加入 $B+B$，至多扣除 $2m+\binom m2$ 次重合，即得上式。若实际有 $t\ge7$ 个级数内点且 $m=12-t$，代入 $t=7,\ldots,12$ 分别得到下界 $43,54,63,70,75,78$。

## 和已有工作的关系

- Clevenger 等已给出有理公比几何级数的两项和唯一性（引理 2.4），以及两个同公比几何轨道的碰撞分类（引理 3.5、推论 3.6）。特别是 $r\ne2$ 时，本文使用的单外点唯一性也可以从其完整轨道分类推出。其推论 3.7 和引理 3.8 讨论两条同公比级数的并。这里逐个处理任意外点，合并非二进与二进公比，用一个无须预设第二条级数的不等式给出最优交点数六。[前一篇论文，第 2–3 节](https://alexricemath.com/wp-content/uploads/2023/08/SPkREVISED3.pdf#page=4)
- 查阅了原作者的四份公开计算笔记及 Kevin O’Bryant 的 1,162,868 组数据。前者支撑十元和十一元问题的证明，后者证明和积对分类完整到六元。公开数据中的十二元实例不能给出无条件下界。[作者代码](https://github.com/Alex-Rice-Millsaps/Sum-Product-Summer-2025) · [O’Bryant 数据与覆盖说明](https://www.math.csi.cuny.edu/~obryant/SumProduct/)
- 截至 2026 年 11 月 27 日，以论文号、题名、作者、`SP(12)`、`12-element`、`41`、`geometric progression`、`sum-product` 等交叉检索公开网页、GitHub Issues/PR 及相关公开代码。精确论文号对应的三个 GitHub issue 是 arXiv 日报。TrureTuring 的 PR 14759 排除七个正实数的和积对 $(23,13)$，PR 14785 处理 O’Bryant 的黄金比例候选，PR 31638 讨论塑料常数的幂。这些公开 AI 结果研究不同的域或参数。EulerSolve 论文目录内未匹配该论文号。[TrureTuring 七元结果](https://github.com/the-omega-institute/trureturing/pull/14759) · [黄金比例问题](https://github.com/the-omega-institute/trureturing/pull/14785) · [代数无理数的幂](https://github.com/the-omega-institute/trureturing/pull/31638) · [EulerSolve 目录](https://eulersolve.org/papers/)
- 直接阅读了 MathDB 365769 的原题和解答区，该页量化任意大基数的正整数集；365772 讨论归一化和积对的极限点。此次公开索引检索未能定位 Antis 等人十二元猜想自身的 canonical 页面，也未找到此处交点上界的已有公开表述。优先权仍有未索引文献与非公开结果带来的不确定性。[MathDB 365769](https://mathdb.com/p/365769/erdos-s-sum-product-conjecture-for-positive-integers) · [MathDB 365772](https://mathdb.com/p/365772/limit-point-conjecture-for-normalized-sum-product-pairs)

## Lean 验证

使用 Lean 和 mathlib 4.24.0，按 `RationalPowers`、`GeometricTranslate`、`SidonGrowth`、`GeometricConcentration`、`TwelveIntegerSets` 的次序编译。主命题为 `SmallSumProduct.twelve_geometric_cap_rat`；正整数原题域的版本为 `SmallSumProduct.twelve_integer_geometric_cap`；任意规模的不等式为 `SmallSumProduct.geometric_growth`；尖锐例子为 `SmallSumProduct.example_sharp`。所有结论通过 Lean 内核，只依赖 `propext`、`Classical.choice`、`Quot.sound`。

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.Nat.ModEq Mathlib.Data.List.Count Mathlib.Data.Rat.Cast.Order Mathlib.Algebra.BigOperators.Group.List.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring Mathlib.NumberTheory.Padics.PadicVal.Basic Mathlib.Data.Finset.Card Mathlib.Data.Finset.Union Mathlib.Tactic.IntervalCases
lake build RationalPowers GeometricTranslate SidonGrowth GeometricConcentration
lake env lean -DwarningAsError=true TwelveIntegerSets.lean
```
