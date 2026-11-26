# Levin 的 Band or Bump 停牌猜想

Bruce Levin 的《The Game of Band or Bump》在 Remark 2 猜想，游戏在第 $n$ 抽首次以 **bump** 停止的联合概率关于 $n$ 对数凹。设有 $m\ge1$ 种牌型，每种 $s\ge1$ 张；所有牌有不同标号，洗匀后不放回抽取。当每类计数均属于 $[\ell,u]$ 时出现 band，有一类计数达到 $u+1$ 时出现 bump，以先发生的事件结束游戏。本文给出所有 $0\le\ell\le u\le s$ 的证明，包含原文两种标准扑克牌例子。 [原文与版本记录](https://arxiv.org/abs/2407.08062) · [第 7 页的 Remark 2](https://arxiv.org/pdf/2407.08062#page=7) · [哥伦比亚大学技术报告 B-256](https://www.columbia.edu/~bl6/appendices/Tech%20Report%20B-256%20The%20Game%20of%20Band%20or%20Bump.pdf)

**定理。** 记 $p_n=\Pr(N=n,\mathrm{bump})$，并令 $p_0=0$。对每个 $n\ge0$ 均有 $p_np_{n+2}\le p_{n+1}^2$。在 $1\le\ell\le u<s$ 时，$p_n>0$ 当且仅当

$$m\ge2,\qquad u+1\le n\le(m-1)u+\ell.$$

原作者在区间 $m\ell\le n\le (m-1)u+\ell$ 提出猜想，上式涵盖实际支集的全部抽牌时刻。若 $u=0$，第一抽必 bump；若 $\ell=0<u$，第一抽必 band；若 $u=s$，不能出现 bump。以下推导处理 $1\le\ell\le u<s$。

## 从抽牌到生成多项式

令 $h=m-1$。固定第 $n$ 张抽出的具体牌。其余牌中，前 $n-1$ 张组成一个均匀无序子集。因为第一次越过上限必须由第 $n$ 张触发，同型牌先前应恰有 $u$ 张。其余 $h$ 类各不超过 $u$，并有至少一类不足 $\ell$。这些条件还保证每个先前前缀都未出现 band 或 bump。任意选定的最后牌都有同样的条件概率，可经牌型与同型标号的双射互换。

设 $F,G,L$ 为单个未被指定牌型的三个计数多项式

$$F=\sum_{i=0}^u\binom si x^i,\qquad
G=\sum_{i=\ell}^u\binom si x^i,\qquad
L=F-G.$$

因此 $P_h=F^h-G^h$ 的 $k$ 次系数 $a_{h,k}$，是所有未超过上限且有至少一类不足 $\ell$ 的 $k$ 张牌手数。对 $k=n-1-u\ge0$ 有

$$p_{u+1+k}=\frac{\binom{s-1}{u}\,a_{h,k}}{\binom{(h+1)s-1}{u+k}}.$$

对 $h\ge1$，$a_{h,k}>0$ 的支集是 $0\le k\le(h-1)u+\ell-1$。固定一类最多取 $\ell-1$ 张、其余每类最多取 $u$ 张，能实现这一区间的每个整数；任何满足缺额条件的牌手也都服从这个总数上界。

## 为什么缺额条件保持对数凹

证明会给出更强的结论：对每个 $h\ge1$，归一化数列 $a_{h,k}/\binom{hs}{k}$ 关于 $k$ 对数凹。这称为相对于容量 $hs$ 的超对数凹性。

对非负系数多项式 $A=\sum a_i x^i,B=\sum b_i x^i$，写 $A\preceq B$ 表示对每个 $i\le j$ 都有 $b_i a_j\le a_i b_j$。在共同正支集上，这就是似然比 $b_i/a_i$ 递增。这个次序可以与具有连续支集的对数凹序列卷积，并对同侧的非负和封闭。特别地，若四个因子都对数凹且 $A\preceq B,C\preceq D$，则 $AC\preceq BD$。其有限和证明是二阶行列式恒等式

$$(\sum f_ip_i)(\sum g_iq_i)-(\sum f_iq_i)(\sum g_ip_i)
=\sum_{i<j}(f_ig_j-f_jg_i)(p_iq_j-p_jq_i).$$

对系数的移位矩阵应用此式即可；对数凹及连续支集保证需要的二阶子式非负。Lean 文件从零延拓的整数下标起独立推导了这些事实。

令 $\delta=u-\ell+1$。有 $F\preceq G$，因为 $G$ 去掉了 $F$ 的初始一段。还有 $F\preceq x^\delta L$：移位后的 $L$ 的正支集从 $\delta$ 延伸到 $u$，在重叠部分，$\binom{s}{i-\delta}/\binom si$ 随 $i$ 递增。此外，右端点为 $b$ 的任何非负序列都满足 $A\preceq x^b$。

归纳中同时维持 $P_h$ 的对数凹性以及两条次序

$$P_h\preceq x^{\ell-1}G^{h-1},\qquad F^h\preceq x^\delta P_h.$$

当 $h=1$ 时，$P_1=L$，两式由上述单牌型比较给出。增加一个牌型时使用两种正项分解

$$P_{h+1}=F P_h+L G^h=L F^h+G P_h.$$

1. 第一种分解的两项分别受 $x^{\ell-1}G^h$ 控制：比较 $F$ 与 $G$、$P_h$ 与 $x^{\ell-1}G^{h-1}$，以及 $L$ 与 $x^{\ell-1}$。故 $P_{h+1}\preceq x^{\ell-1}G^h$。
2. 将第二种分解整体乘以 $x^\delta$。$F^{h+1}$ 分别先于 $(x^\delta L)F^h$ 和 $G(x^\delta P_h)$，所以 $F^{h+1}\preceq x^\delta P_{h+1}$。
3. 再用第二种分解。$LF^h\preceq x^{\ell-1}(x^\delta P_h)=x^uP_h$，而 $GP_h\preceq x^uP_h$。从而 $P_{h+1}\preceq x^uP_h$。

现在考虑向一个合格牌手添加一张牌。在单个类型已达到 $u$ 时，再抽同型牌会越过上限。在恰有一个类型不足 $\ell$、其计数为 $\ell-1$ 时，再抽该型牌会补齐最后一类。这两个互不重叠的失败原因给出从 $j$ 个类型的合格牌手出发的失败扩展数多项式

$$B_j=j\left[(s-u)\binom su x^u P_{j-1}
+\ell\binom s\ell x^{\ell-1}G^{j-1}\right].$$

第二项的权重也等于 $(s-\ell+1)\binom{s}{\ell-1}$。取 $j=h+1$，上面的第 1 和第 3 步给出 $P_j\preceq B_j$。令 $a_k=[x^k]P_j$、$b_k=[x^k]B_j$。双计数合法的一步扩展得到

$$(k+1)a_{k+1}=(js-k)a_k-b_k.$$

在正支集内，$b_k/a_k$ 递增。于是 $a_{k+1}/a_k=(js-k-b_k/a_k)/(k+1)$ 递减，从而完成下一步归纳所需的普通对数凹性。进一步，把 $a_k$ 除以 $\binom{js}{k}$，其相邻比为

$$1-\frac{b_k}{(js-k)a_k}.$$

它也递减，这就证明了超对数凹性。支集外的零项直接满足相邻不等式。

最后，从未被指定牌型的系数回到补入最后牌类型的抽牌概率。额外因子 $\binom{hs}{k}/\binom{(h+1)s-1}{u+k}$ 的相邻比为

$$\frac{u+k+1}{k+1}\cdot\frac{hs-k}{(h+1)s-1-u-k}.$$

正项范围内，两因子都递减，因为 $s-1-u\ge0$。将这个正对数凹因子和常数 $\binom{s-1}{u}$ 乘到归一化数列便得结论。Lean 通过相同的扩展计数，把计数恰为 $u$ 的标记牌型作为一个精确区间合并，得到同一概率。

## Lean 与精确复验

[BandOrBumpAll.lean](BandOrBumpAll.lean) 是独立源文件。Lean 4.24.0 与 mathlib v4.24.0 下，八项公理检查均只出现 `propext`、`Classical.choice`、`Quot.sound`。在带有相应依赖的 Lake 项目内执行

```sh
lake env lean -DwarningAsError=true BandOrBumpAll.lean
python3 check_all_ranks.py
```

| 声明 | 形式化内容 |
| --- | --- |
| `BandAll.all_legal_thresholds` | $m,s\ge1$、$0\le\ell\le u\le s$ 的完整对数凹命题 |
| `BandAll.all_ranks_bump_log_concave`、`BandAll.all_ranks_support` | 从实际标号牌手直接得到的全牌型数不等式与精确正支集 |
| `BandAll.missing_log_concave` | $P_h$ 相对于 $hs$ 的超对数凹性 |
| `BandAll.bump_hand_iff_first_bump` | 任一符合该牌手的牌序在每个此前前缀都未停止，且末张首次造成 bump，当且仅当牌手属于计数分子 |
| `BandAll.probability_is_card_ratio`、`BandAll.all_final_cards_ratio` | 分子与分母均为同一标号样本空间的有限基数，均匀平均全部可能末牌保持该比值 |
| `BandAll.remainingDeckEquiv` | 对任意原始牌型、标号的末牌，删去它与分类型重新标号之间的显式双射 |

不放回洗牌下，固定末牌和前 $t$ 张的无序子集后，仍有 $t!\,(ms-t-1)!$ 种等可能牌序，故有限牌手模型给出原始随机排列中的概率。Lean 中的计数对象是标号子集及其有序牌型列表，核验了最后牌的双射、对全部末牌的平均和逐前缀判据。 [内核输出](lean-check-all.txt)

独立的 Python 程序逐张抽牌，以占用数直方图计算每种后继的精确条件概率；它逐时刻与牌手多项式、正支集和相邻不等式对照。在 $1\le m\le9,1\le s\le7$ 上含边界的 1,071 组完整参数全部通过。另测 $m=24,s=3$、$m=2,s=40$ 和论文的两个 52 张牌局。四花色玩法 $(4,13,5,8)$ 的总 bump 概率为 $532134081359/1350540667070\approx0.394015593$；十三牌型玩法 $(13,4,1,3)$ 为 $1309858309850791/2149964274784935\approx0.609246547$。 [独立核查程序](check_all_ranks.py) · [原文 Table 1](https://arxiv.org/pdf/2407.08062#page=2)

## 公开先例检索

截至 2026 年 11 月 27 日，按作者、arXiv 编号、游戏的两个名称、`bump stopping time`、`log-concavity`、`likelihood ratio`、有限占用模型、全类型阈值与两个超几何矩形之差等组合检索了可访问的公开材料。最接近的正式结果是 Levin 的多元超几何矩形定理；原作者在本题 Remark 2 引用它来处理 band 概率，并将 bump 的联合概率单列为猜想。本证明处理的 $F^h-G^h$ 是有至少一类不足的新约束。从作者论文目录和所检索的 arXiv、出版商网页中未查到一般情形的在先证明。 [作者的出版目录](https://www.columbia.edu/~bl6/publist.htm) · [2024 年矩形定理](https://doi.org/10.1080/07474946.2024.2379901) · [原文 Remark 2](https://arxiv.org/pdf/2407.08062#page=7)

GitHub 全局代码检索的相关命中包括原论文的 arXiv 标识符与 RSS 摘要镜像。对 `1337isnot1337/solved-conjectures` 和 TrureTuring 的公开代码及 Issues 检索没有命中这一证明。以题名、作者加超几何停止时刻、旧游戏名和编号检索 MathDB 的公开网页索引，未定位可确认的题目原页；该项核查未覆盖订阅数据库快照。检索不能排除未发表或尚未索引的先例。 [公开 RSS 镜像](https://github.com/ehijano/rss_fetch/blob/2820b6d225aac11cdc3f9e8f0136ff031869cee9/rss_data/stat.AP/2024-07-11_stat.AP.xml) · [TrureTuring](https://github.com/the-omega-institute/trureturing) · [solved-conjectures](https://github.com/1337isnot1337/solved-conjectures) · [MathDB](https://mathdb.com/database)

OpenAlex 在本次检索中列出的唯一引用论文为上述矩形定理。可从固定元数据记录查看后续引用。[OpenAlex 原条目](https://openalex.org/W4400611359)
