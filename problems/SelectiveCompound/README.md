# 任意有限公平博弈与 Nim 堆的选择复合有精确阈值

Beideman、Bowen、Müyesser 在 2020 年论文的第 3.1 节 Question 3 询问，固定一个公平博弈局面 $A$，给它附加一个含 $k$ 枚石子的 Nim 堆，哪些 $A$ 会在 $k$ 充分大时达到最长对局长度所给的 Grundy 上界？在选择复合中，一步可以只走原博弈、只减少 Nim 堆，也可以两者同时进行。原论文的 Theorem 2 已经解决 $A$ 为有限多个 Nim 堆的通常析取和的情形。[期刊原文，第 2–3、12、18–19 页](https://math.colgate.edu/~integers/ug4/ug4.pdf) · [arXiv:1802.08700](https://arxiv.org/abs/1802.08700)

## 结论

令 $d(A)$ 为从 $A$ 出发的最大剩余步数，令 $g_A(k)$ 为它与大小 $k$ 的 Nim 堆选择复合后的 Sprague–Grundy 值。**深度恰为 $d$ 的全部有限局面共同适用的最小阈值是 $\lfloor d^2/4\rfloor$。** 任意 $A$ 和 $k\ge\lfloor d(A)^2/4\rfloor$ 都满足 $g_A(k)=k+d(A)$。对每个深度，还存在一个明确的局面，使得等式对所有比该阈值小的堆都失效。

一套游戏规则可以有无穷多个初始局面。Lean 模型要求每个局面有有限个合法后继，且走法良基，它从这两个条件构造局面的深度和 Grundy 值。

对一整套规则，量词顺序会改变答案。若每个局面的合法步数都有一个共同上界 $M$，则

$$
\bigl[\exists K\ \forall k\ge K\ \forall A,\quad g_A(k)=k+d(A)\bigr]
\quad\Longleftrightarrow\quad
\bigl[\exists D\ \forall A,\quad d(A)\le D\bigr].
$$

例如，设原游戏每次必须且只能取一枚石子，初始有 $n$ 枚。每个固定 $n$ 都满足第一条定理。但对任意给定的 $k$，选 $n=k+2$，复合局面至多有 $2k+1$ 个合法后继，其 Grundy 值严格小于 $k+n=2k+2$。这与原文第 3.2 节 Theorem 6 相容。该定理固定 $k$，研究减法游戏参数 $n$ 的周期性。Question 3 写出的次序则先固定 $A$，再让 $k$ 增大；在原文紧接着的周期性讨论中，这两个方向需要区分。[期刊原文，第 18–19 页](https://math.colgate.edu/~integers/ug4/ug4.pdf#page=18)

## 固定局面的充分阈值

1. 从 $(A,k)$ 可以走到 $(A,j)$ 的每个 $j<k$，也可以走到 $(B,j)$ 的每个 $A\to B$ 和 $j\le k$。增加一枚堆石后，所有原先可达的 Grundy 值仍然可达，又新增原局面的值。因此 $g_A(k+1)>g_A(k)$，从而 $g_A(k)\ge k$。复合局面的最长对局恰为 $k+d(A)$，因而 $g_A(k)\le k+d(A)$。
2. 按 $d(A)$ 归纳。深度 $0$ 时上下界相等。若 $d(A)=d+1$，取一个深度 $d$ 的后继 $B$。对每个 $j\ge\binom d2$，归纳假设给出 $g_B(j)=j+d$。若 $k\ge\binom{d+1}2=\binom d2+d$，并假定 $v=g_A(k)<k+d+1$，则 $j=v-d$ 落在 $[\binom d2,k]$。这样 $(A,k)$ 有一步能到达值也为 $v$ 的 $(B,j)$，和 mex 的定义矛盾。
3. 若原局面的合法步数为 $b(A)$，复合局面至多有 $k+(k+1)b(A)$ 个合法后继。若大小为 $K$ 的堆已经对所有局面达到上界，便有 $d(A)\le(K+1)b(A)\le(K+1)M$。反方向应用第一条定理及二项式系数的单调性。

第 2 步采用原论文 Theorem 2 在辅助 Nim 情形中用一个后继覆盖连续 Grundy 值区间的归纳思路，先得到 $\binom d2$ 这一充分上界。[原论文 Theorem 2 的证明](https://math.colgate.edu/~integers/ug4/ug4.pdf)

## 最优上界

由于 $g_A(k)$ 随 $k$ 严格增加，可以逐个扫描输出标签 $0,1,\ldots$。记 $h_A(n)$ 为小于 $n$ 却没有出现在这行中的标签数。若 $g_A(k)=n$，则 $n-h_A(n)=k$。由 $g_A(k)\le k+d(A)$ 得 $h_A(n)\le d(A)$。对任意一步 $A\to B$，若 $A,B$ 两行都取到标签 $n$，则 $B$ 必须在更大的堆才取到它，否则 $(A,k)$ 就能一步走到相同值。用漏掉的标签数写，这给出 $h_B(n)<h_A(n)$。

对任意局面 $A$，以下更细的命题控制其尚未稳定的一段。设 $d=d(A)$ 且 $h_A(n)<i\le d$，则存在整数 $0\le u\le i$ 使

$$
n-h_A(n)\le u(d-u).
$$

按深度归纳。设父局面深度为 $d+1$，选一个深度为 $d$ 的后继 $B$。在 $h_B(n)\ge h_A(n)$ 的时刻，考虑

$$
n-h_A(n)+d-h_B(n).
$$

当两行的这一大小关系持续时，父行每使用一个标签，子行必须漏掉它，所以该量不会增加。初值为 $d=1\cdot((d+1)-1)$。若大小关系刚从 $h_B<h_A$ 切换为 $h_B\ge h_A$，则在这一步前父行已漏 $q$ 个，子行漏 $q-1$ 个。父行使用当下的标签，子行把漏数增至 $q$。此时父行已使用的标签数等于上一步之前子行已使用的标签数。深度归纳给出后者至多 $u(d-u)$，其中 $u\le q$。加上剩余的 $d-q$ 至多得到 $(u+1)(d-u)$，而 $u+1\le i$。在 $h_B<h_A$ 的时刻，父行已使用的标签数则直接由子行控制。这样覆盖扫描中的每一步。

若 $g_A(k)<k+d$，取 $n=g_A(k)+1$。父行已经使用 $k+1$ 个标签，并且漏掉的还不到 $d$ 个。取 $i=d$ 就有 $k+1\le u(d-u)\le\lfloor d^2/4\rfloor$。因此当 $k\ge\lfloor d^2/4\rfloor$ 时只能达到 $k+d$。

## 达到上界的游戏

固定 $m$。一个石堆若有至多 $m$ 枚，按普通 Nim 规则可以取走任意正数枚；若有多于 $m$ 枚，每步恰好取走一枚。在初始堆上再加 $r$ 枚强制先走的石子，使初始深度为 $m+r$。对 $1\le r\le m+1$，它与另一个大小为 $k$ 的普通 Nim 堆选择复合以后，

$$
g_{m,r}(k)=k+m+r \quad\Longleftrightarrow\quad k\ge mr.
$$

其归纳证明还给出跃升之前的最后一段。对所有 $k<mr$ 有 $g_{m,r}(k)\le k+r-1$，并在 $m(r-1)\le k<mr$ 时取等号。增加一道强制步时，旧局面变成唯一的原游戏后继。在 $k<m(r+1)$ 的范围内，新局面的候选值 $k+r$ 处于旧局面的低值和已经跃升的高值之间；更小堆上的新局面同样达不到此候选值。由 mex 得到低段上界。取边界 $k=mr-1$，旧行的线性段覆盖新局面可能低于 $k+r$ 的每一个候选值，于是新行达到 $k+r$。严格单调性把该下界传到后面。到 $k=m(r+1)$ 后，旧行跃升后的连续值区间迫使新行也达到最大值。

对 $d=2m>0$ 取 $r=m$，所需阈值为 $m^2$。对 $d=2m+1$ 取 $r=m+1$，阈值为 $m(m+1)$。深度零时游戏只有 Nim 分量，阈值为零。两种奇偶性正好给出每个 $d$ 的 $\lfloor d^2/4\rfloor$。

## 形式化与复验

完整文件 `SelectiveCompound.lean` 自包含，内核从合法走法递归定义最长对局长度和普通 mex Grundy 函数。选择复合在 `Game.withHeap_move_iff` 中描述。`Game.large_heap_grundy_optimal` 对任意局面给出充分界，`QuadraticFamily.exact_witness_at_every_depth` 给出每个深度的匹配见证，`QuadraticFamily.universal_cutoff_iff` 合并了两端。全规则族的量词问题由 `Game.uniform_cutoff_iff_bounded_depth` 证明。`lean-check.txt` 记录十二项定理的公理审计，仅出现 `propext`、`Classical.choice` 和 `Quot.sound`。

独立下载包锁定 Lean 4.24.0 和 mathlib 的提交。进入包目录运行。

```sh
lake exe cache get Mathlib.Data.Finset.Lattice.Fold Mathlib.Data.Finset.Prod Mathlib.Data.Finset.Card Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Find Mathlib.Tactic.ByContra Mathlib.Algebra.Order.Ring.Unbundled.Basic Mathlib.Algebra.Order.Ring.Nat Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true SelectiveCompound.lean
python3 check_compound_optimal.py
```

独立 Python 脚本直接列出每一个合法局面并取 mex。它枚举有六个已按拓扑顺序标号的顶点的全部 32,768 个有向无环图，对每个图中六个局面、堆大小 $0,\ldots,12$ 共核对 2,555,904 次。所有图中深度 0 至 5 的最坏阈值依次是 0、0、1、2、4、6。另以 $k=0,\ldots,64$ 核对显式减法反例，对 153 个强制步局面又逐项核对 22,236 个最小阈值等价式。一般参数由 Lean 证明覆盖。

## 公开先例检索

截至 2026-11-27，检索覆盖原题号、作者、论文编号，以及 `auxiliary Nim`、`auxiliary G`、`selective sum/compound` 结合同 `depth/birthday`、`large heap`、`threshold` 等表述，也检索了 `sharp quadratic threshold`、`maximal threshold`、`selective compound` 与 `sequential game` 及 `floor` 的组合。可查到的最接近结果如下。

- 原作者证明了由任意多个普通 Nim 堆组成的特例。Boros 等研究了 proper Nim 的额外可选堆，也给出特定超图 Nim 的选择复合公式。OpenAlex 将这两项列为原预印本的施引工作。Müyesser 的书目链接回原文。[作者主页](https://alpmuye.github.io/) · [proper Nim 的扩展](https://doi.org/10.1007/s00182-020-00707-3) · [超图 Nim 的选择复合](https://arxiv.org/abs/1903.08138) · [原预印本的 OpenAlex 记录](https://openalex.org/W2788705627)
- Boros 等还给出超图复合在每个分量的 Grundy 值随每步严格下降时的化约。这里允许走向 Grundy 值较高的后继，例如只能取一枚的偶数局面。[期刊原文](https://link.springer.com/article/10.1007/s00182-023-00850-7)
- GitHub 公开代码和 Issues 的定向检索覆盖 `the-omega-institute/trureturing` 与 `1337isnot1337/solved-conjectures`。全局代码检索中的题号命中包括作者书目及通用论文数据集的处理记录。这些检索没有找到本文点态命题的既有证明。[TrureTuring](https://github.com/the-omega-institute/trureturing) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures)
- MathDB 公开的周期性目录列出了同文的星形 Kayles 条目 #338530，以及固定一枚附加堆的 Kayles 条目 #338531。两项都是第 3.2 节的问题。通过公开目录、作者/题名及等价措辞检索，未识别出第 3.1 节 Question 3 的独立题页。上述两个 Kayles 页面在本次访问均返回缓存错误或浏览器验证页，因此未能读取各自的 Solutions 标签。检索覆盖公开网页，不能排除未索引、私有或未发表的解答。[MathDB 周期性目录](https://mathdb.com/database?tag=periodicity) · [MathDB Sprague–Grundy 目录](https://mathdb.com/database?tag=sprague-grundy-theory)
