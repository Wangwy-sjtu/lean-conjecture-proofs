# 完全多部图获得完美消去序的最少补点数与最少补边数

设完全多部图的两个最大部大小为 $a\ge b\ge1$，其余所有部的顶点总数为 $r$。每添加一个全邻接顶点，就把它与此前的所有顶点相连。包括新增顶点之间的连边在内，这等价于增加一个单点部。

**最少需要添加 $\max(0,b-1-r)$ 个顶点。** 特别地，原图具有完美消去序当且仅当 $r\ge b-1$。例如 $K_{4,4}$ 需要三个全邻接顶点，$K_{4,4,2}$ 需要一个，而 $K_{4,4,3}$ 已经具有这种排序。只有一个部的独立图也已具有这种排序。

Cao、Lu、Nie、Sun 和 Tian 在研究 CNOT 奇偶网络时提出了这个最小添加数问题，输入可以是任意图。上述结果解决了完全多部图这一整个图族。arXiv 版本将问题放在第 4 节命题 4.1 之后，作者网站的稿本将其放在命题 19 之后。[原始预印本](https://arxiv.org/abs/2509.10070) · [作者网站稿本](https://yiren.lu/assets/pdf/parity-network.pdf)

原论文紧接着问，只在原有顶点之间补边能否也获得所需排序。对所有完全多部图，这个问题的最少补边数也恰为 $\max(0,b-1-r)$。补点与补边是两种不同的操作，每次分别只允许其中一种。补边定理按原有顶点的身份计算不同的无向边。

## 与量子电路的联系

给定顶点排序，对每个顶点 $v$，删除 $v$ 并逐个考察所得连通分量。在各分量内，把排在 $v$ 后面的邻居按原顺序列出，要求列表中每两个相继顶点相邻。满足此条件的排序称为 *perfect cancellation ordering*，这里译作“完美消去序”。

原论文证明，如果一个连通图有这种序，则可构造恰用 $m+n-1$ 个 CNOT 门的最优图奇偶网络，其中 $m$ 和 $n$ 分别为该图的边数和顶点数。因而上面的阈值给出完全多部图满足这一构造条件所需的最小扩充。若扩充量低于阈值，所排除的是完美消去序。图仍能否通过其他构造达到相同门数，涉及原论文另列的主猜想。[定义与网络构造](https://arxiv.org/pdf/2509.10070)

## 证明

把每个顶点标记为其所属部。两个不同顶点有边恰好意味着它们的标记不同。新增 $k$ 个点后，两个最大原部以外共有 $r+k$ 个顶点。

**下界。** 当 $b\ge2$ 时，任取一个排序，令 $v$ 为两个最大部中最早出现的顶点。删除 $v$ 后两个部仍非空，从而剩余图连通。另一个大部中至少有 $b$ 个顶点，它们全是 $v$ 的后继邻居，彼此之间却没有边。在 $v$ 的后继邻居列表中，连续两次出现该部之间都需要一个来自其他部的顶点。至少需要 $b-1$ 个这样的顶点，故 $r+k\ge b-1$。对于 $b=1$，下界为零。

**构造。** 假设 $r+k\ge b-1$，把两大部记为 $A,B$。先预留 $b$ 行，给每一行写下 $A,B$ 两个标记。其余每个部的大小至多为 $b$，因此可以将这个部的顶点分到不同的行，尽量先占用还没有第三个标记的行。分配完毕后至少 $b-1$ 行有第三个标记。把唯一可能没有附加标记的行排到最后，然后逐行读取，最前面再添上 $a-b$ 个 $A$。

例如 $K_{5,4,2}$ 补一个全邻接顶点后可取

$$
A\;|\;ABC\;|\;ABC\;|\;ABD\;|\;AB .
$$

竖线只标出构造中的前缀和各行，$D$ 为新增点。对任一顶点，后继邻居的标记序列由其后缀删去自身标记得到。删去 $A$ 时，各行以 $B$ 起头，行间由前一行的附加标记隔开。删去 $B$ 时同理。删去其他标记时，每行留下 $A,B$，足以隔开两行中可能相同的标记。每行内都没有同部重复，因此所有后继邻居列表中相继的标记均不同，构成所需排序。

## 只补边的精确最优值

**下界。** 任何新增边都位于某个原有部之内。若有正的下界，则 $b\ge2$。令 $v$ 为排序中最先属于两个大部之一的顶点。删去 $v$ 后两个部都仍非空，原图因而连通，新增边会保留这种连通性。另一个大部至少有 $b$ 个顶点，它们都是 $v$ 的后继邻居。在这个邻居列表中，这些顶点的相继出现产生至少 $b-1$ 个间隔。若某一间隔没有其他顶点隔开，就必须新增一条该部内部的边。若有顶点隔开，可以取其中一个，大部以外的原有顶点最多贡献 $r$ 次；若它来自 $v$ 所在的部，成为 $v$ 的邻居又要求一条以 $v$ 为端点的新增边。不同间隔耗用不同顶点或不同新增边。于是至少须添 $b-1-r$ 条边。

**构造。** 只需考虑 $b>r+1$。把第二大部暂缩到 $r+1$ 个顶点。补点证明里的排序构造此时恰好用尽了所有分隔顶点，其末项 $y$ 属于第二大部。在这个末项后接回暂时拿掉的所有顶点，把 $y$ 和这些顶点依次连成一条路径，一共新添 $b-1-r$ 条边。前面每个顶点要么看到整条路径作为连续的一段后继邻居，要么和该路径同部、因而看不到其中任何顶点。路径中的顶点自己至多有一个更晚的邻居。这个顺序因此满足论文的定义。对 $K_{4,4,2}$，可以依次排列为 $A\mid ABC\mid ABC\mid ABB$，仅把最后两个 $B$ 顶点相连。对 $K_{a,b}$，可先列出全部 $A$，再把全部 $B$ 连成一条路径。

在 $K_{2,p}$ 这个特例中，作者的稿本图 2 已指出，只补两点部中的一条边便得到弦图，从而构造了 $3p+2$ 门的电路。本文的固定顶点定理覆盖任意 $b$ 和任意其他部，并同时给出最优性的下界。[作者图 2 和 §2.1](https://yiren.lu/assets/pdf/parity-network.pdf)

这也给出原图的电路上界。设连通完全多部图有 $n$ 个顶点、$m$ 条边，记 $k=\max(0,b-1-r)$。给原图添这 $k$ 条边，再用 Cao 等人的定理，可得恰用 $m+k+n-1$ 个受控非门的电路。该电路会实现原图要求的每个边奇偶量，并复原输入。故原图最优门数在 $m+n-1$ 与 $m+n-1+k$ 之间。这里使用了原论文关于图与电路的定理；随包 Lean 代码验证的是上面两种图扩充的精确阈值。[图奇偶网络定义与定理 1.4](https://arxiv.org/html/2509.10070v1#S1)

## Lean 核验

[Multipartite.lean](./Multipartite.lean) 包含对任意有限部数和任意部大小的证明。`classification` 给出原图分类，`least_universal` 证明最小数可达。`graphOrdering_iff` 把颜色词检验与原论文对各连通分量的定义相连，`graph_universal_completion` 直接对逐个命名的顶点与真实图路径陈述充要条件。除了通用证明，独立枚举还交叉检查了总顶点数 2 至 9、至少两个非空部的全部 87 种部大小分拆。

源文件末尾的 `#print axioms` 会在复验时输出每个主定理的公理依赖。随包版本只列出 `propext`、`Classical.choice` 和 `Quot.sound`。

## 公开在先结果核查

截至 2026-11-27，在下列搜索中未发现相同的完全多部图分类或最小添加数公式。检索覆盖可公开访问和索引的材料，无法排除未公开或未被索引的工作。

| 来源 | 最接近的结果 |
| --- | --- |
| 作者、论文与出版索引 | 比对了 arXiv、作者网站的两个稿本、作者出版清单和 DBLP。原文给出适用于一般图的充分条件，随后明确提出最小添加数问题。作者主页将此项列为手稿。[作者稿本](https://yiren.lu/assets/pdf/parity-network.pdf) · [作者简历](https://yiren.lu/cv/) · [DBLP](https://dblp.org/rec/journals/corr/abs-2509-10070) |
| 按数学内容检索 | 检索 `perfect cancellation ordering`、`perpane`、`complete multipartite`、`complete bipartite`、`co-cluster graph`、`universal completion`、`consecutive later neighbors` 及其组合。返回的原论文定理说明何时可从排序构造最优网络，未给出该图族的所求阈值。[原始定义与开放问题](https://arxiv.org/pdf/2509.10070) |
| GitHub 与公开 AI 记录 | GitHub Code 对 `"perfect cancellation ordering" "multipartite"` 未命中。对 `"graphic parity network" "complete bipartite"` 的命中为一份汇集多篇摘要的 RSS 档案，两个短语来自不同论文。另检索公开 GitHub Issues、1337isnot1337/solved-conjectures 和 TrureTuring。后者最接近的公开工作讨论反射对称对角酉矩阵的最坏 CNOT 数，问题与此不同。[GitHub 解题项目](https://github.com/1337isnot1337/solved-conjectures) · [TrureTuring 邻近题目](https://www.trureturing.org/research/huang-kosugi-nishi-matsushita-2024-reflection-diagonal-cnot-lower-bound/) |

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Order.Bounds.Defs Mathlib.Data.List.Chain Mathlib.Data.List.Nodup
lake env lean -DwarningAsError=true Multipartite.lean
```

补边文件 [MultipartiteEdges.lean](MultipartiteEdges.lean) 在原有命名顶点上使用由无序端点对组成的有限集合，要求每个成员确是原图内的缺边。主定理 `edge_completion_iff` 与 `least_inserted_edges` 给出必要充分条件和可达到的最优值。独立的直接枚举检验了总顶点数 2 至 9 的所有 87 种非平凡分拆。该检验逐一尝试低于候选值的边集，对每个候选图按原始的删点连通分量定义搜寻顶点排列。

```sh
lake exe cache get Mathlib.Data.Finset.Card Mathlib.Data.List.Chain Mathlib.Data.List.Nodup Mathlib.Order.Bounds.Defs
lake build Multipartite
lake env lean -DwarningAsError=true MultipartiteEdges.lean
```

补边定理另以 `perfect cancellation ordering`、`edge completion`、`complete multipartite`、`complete bipartite` 及相关用语检索 arXiv、GitHub 的默认分支代码和公开 Issues。相关论文检索返回作者原问题；GitHub 的双关键词查找未返回相同图族的阈值。较宽泛的组合命中论文聚合页面和全文索引。TrureTuring 与公开数学证明库中未检出这一精确补边数。一般图是否总能用至多 $m$ 条新增边完成，仍是原论文留给任意图的问题。[原论文的两个扩充问题](https://arxiv.org/html/2509.10070v1#S4) · [GitHub 代码检索](https://github.com/search?q=%22perfect+cancellation+ordering%22+%22multipartite%22&type=code) · [GitHub 讨论记录检索](https://github.com/search?q=%22perfect+cancellation%22+%22multipartite%22&type=issues)
