# 大 Nim 堆与任意有限公平博弈的选择复合

Beideman、Bowen、Müyesser 在 2020 年论文的第 3.1 节 Question 3 询问，固定一个公平博弈局面 $A$，给它附加一个含 $k$ 枚石子的 Nim 堆，哪些 $A$ 会在 $k$ 充分大时达到最长对局长度所给的 Grundy 上界？在选择复合中，一步可以只走原博弈、只减少 Nim 堆，也可以两者同时进行。原论文的 Theorem 2 已经解决 $A$ 为有限多个 Nim 堆的通常析取和的情形。[期刊原文，第 2–3、12、18–19 页](https://math.colgate.edu/~integers/ug4/ug4.pdf) · [arXiv:1802.08700](https://arxiv.org/abs/1802.08700)

## 结论

令 $d(A)$ 为从 $A$ 出发的最大剩余步数，令 $g_A(k)$ 为它与大小 $k$ 的 Nim 堆选择复合后的 Sprague–Grundy 值。**对每个有限局面 $A$，只要 $k\geq\binom{d(A)}2$，就有 $g_A(k)=k+d(A)$。** 一套游戏规则可以有无穷多个初始局面。Lean 模型只要求每个局面有有限个合法后继，且走法良基。阈值对相同深度的所有局面同时成立。

对一整套规则，量词顺序会改变答案。若每个局面的合法步数都有一个共同上界 $M$，则

$$
\bigl[\exists K\ \forall k\ge K\ \forall A,\quad g_A(k)=k+d(A)\bigr]
\quad\Longleftrightarrow\quad
\bigl[\exists D\ \forall A,\quad d(A)\le D\bigr].
$$

例如，设原游戏每次必须且只能取一枚石子，初始有 $n$ 枚。每个固定 $n$ 都满足第一条定理。但对任意给定的 $k$，选 $n=k+2$，复合局面至多有 $2k+1$ 个合法后继，其 Grundy 值严格小于 $k+n=2k+2$。这与原文第 3.2 节 Theorem 6 相容。该定理固定 $k$，研究减法游戏参数 $n$ 的周期性。Question 3 写出的次序则先固定 $A$，再让 $k$ 增大；在原文紧接着的周期性讨论中，这两个方向需要区分。[期刊原文，第 18–19 页](https://math.colgate.edu/~integers/ug4/ug4.pdf#page=18)

## 证明

1. 从 $(A,k)$ 可以走到 $(A,j)$ 的每个 $j<k$，也可以走到 $(B,j)$ 的每个 $A\to B$ 和 $j\le k$。增加一枚堆石后，所有原先可达的 Grundy 值仍然可达，又新增原局面的值。因此 $g_A(k+1)>g_A(k)$，从而 $g_A(k)\ge k$。复合局面的最长对局恰为 $k+d(A)$，因而 $g_A(k)\le k+d(A)$。
2. 按 $d(A)$ 归纳。深度 $0$ 时上下界相等。若 $d(A)=d+1$，取一个深度 $d$ 的后继 $B$。对每个 $j\ge\binom d2$，归纳假设给出 $g_B(j)=j+d$。若 $k\ge\binom{d+1}2=\binom d2+d$，并假定 $v=g_A(k)<k+d+1$，则 $j=v-d$ 落在 $[\binom d2,k]$。这样 $(A,k)$ 有一步能到达值也为 $v$ 的 $(B,j)$，和 mex 的定义矛盾。
3. 若原局面的合法步数为 $b(A)$，复合局面至多有 $k+(k+1)b(A)$ 个合法后继。若大小为 $K$ 的堆已经对所有局面达到上界，便有 $d(A)\le(K+1)b(A)\le(K+1)M$。反方向应用第一条定理及二项式系数的单调性。

第 2 步采用原论文 Theorem 2 在辅助 Nim 情形中使用的“大堆向一个后继覆盖连续 nimber 区间”的归纳思路。任意有限局面都具有深度恰小一的后继，这就给出了推广所需的结构。[原论文 Theorem 2 的证明](https://math.colgate.edu/~integers/ug4/ug4.pdf)

## 形式化与复验

`SelectiveCompound.lean` 从合法走法递归定义最长对局长度和普通 mex Grundy 函数。选择复合使用的两类后继由 `Game.withHeap_move_iff` 描述。主定理是 `Game.large_heap_grundy`、`Game.fixed_position_threshold` 和 `Game.uniform_cutoff_iff_bounded_depth`。具体减法反例为 `takeOne_fails_uniformly` 和 `no_uniform_cutoff_for_takeOne`。补充文件 `lean-check.txt` 记录了五个主结果使用的基础公理，其中仅列出 `propext`、`Classical.choice` 和 `Quot.sound`。

独立 Python 脚本直接列出每一个合法局面并取 mex。它枚举有六个已按拓扑顺序标号的顶点的全部 32,768 个有向无环图，对每个图中六个局面、堆大小 $0,\ldots,12$ 共核对 2,555,904 次。另以 $k=0,\ldots,64$ 核对显式减法反例。一般参数由 Lean 证明覆盖。

## 公开先例检索

截至 2026-11-27，检索覆盖原题号、作者、论文编号，以及 `auxiliary Nim`、`auxiliary G`、`selective sum/compound` 结合同 `depth/birthday`、`large heap`、`threshold` 等表述。可查到的最接近结果如下。

- 原作者证明了由任意多个普通 Nim 堆组成的特例。Boros 等研究了 proper Nim 的额外可选堆，也给出特定超图 Nim 的选择复合公式。OpenAlex 将这两项列为原预印本的施引工作。Müyesser 的书目链接回原文。[作者主页](https://alpmuye.github.io/) · [proper Nim 的扩展](https://doi.org/10.1007/s00182-020-00707-3) · [超图 Nim 的选择复合](https://arxiv.org/abs/1903.08138) · [原预印本的 OpenAlex 记录](https://openalex.org/W2788705627)
- Boros 等还给出超图复合在每个分量的 Grundy 值随每步严格下降时的化约。这里允许走向 Grundy 值较高的后继，例如只能取一枚的偶数局面。[期刊原文](https://link.springer.com/article/10.1007/s00182-023-00850-7)
- GitHub 公开代码和 Issues 的定向检索覆盖 `the-omega-institute/trureturing` 与 `1337isnot1337/solved-conjectures`。全局代码检索中的题号命中包括作者书目及通用论文数据集的处理记录。这些检索没有找到本文点态命题的既有证明。[TrureTuring](https://github.com/the-omega-institute/trureturing) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures)
- MathDB 公开的周期性目录列出了同文的星形 Kayles 条目 #338530，以及固定一枚附加堆的 Kayles 条目 #338531。两项都是第 3.2 节的问题。通过公开目录、作者/题名及等价措辞检索，未识别出第 3.1 节 Question 3 的独立题页。上述两个 Kayles 页面在本次访问均返回缓存错误或浏览器验证页，因此未能读取各自的 Solutions 标签。检索覆盖公开网页，不能排除未索引、私有或未发表的解答。[MathDB 周期性目录](https://mathdb.com/database?tag=periodicity) · [MathDB Sprague–Grundy 目录](https://mathdb.com/database?tag=sprague-grundy-theory)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.Finset.Lattice.Fold Mathlib.Data.Finset.Prod Mathlib.Data.Finset.Card Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Find Mathlib.Tactic.ByContra
lake env lean -DwarningAsError=true SelectiveCompound.lean
python3 check_compound.py
```
