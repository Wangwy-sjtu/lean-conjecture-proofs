# 可见下推语言的后缀减法游戏

Yusuke Inoue 与 Hiroki Inazu 在《Word Subtraction Games》第 4 节的 Problem 4.1 询问，哪些包含非正则语言的上下文无关语言子类，可以保证后缀减法游戏的败态语言仍是上下文无关语言。作者已证明正则语言对这一操作封闭，也给出了线性上下文无关语言、确定性上下文无关语言的反例。[原文及问题 4.1](https://arxiv.org/html/2611.09157v1#S4)

**结果。** 固定有限字母表，把字母预先分为入栈、出栈、内部三类。如果允许删除的非空后缀构成可见下推语言（visibly pushdown language，VPL），那么正常玩法下先手必败的输入词构成 VPL，先手必胜的输入词也构成 VPL。两者沿用原来的字母表与分类。该类包含正则语言，也包含非正则语言。这为作者的开放问题给出一个完整的正面例子，原题允许有其他答案。[可见下推语言与上下文无关语言的关系，原论文 §5.1](https://www.cis.upenn.edu/~alur/Jacm09.pdf#page=26)

## 从后缀删除到一个逻辑公式

给定一个长度为 $n$ 的线性输入词 $w$。把入栈字母和与它配对的出栈字母连边，两端之间是一段完整的、允许含内部字母的配对词。输入可以有未配对的入栈或出栈字母。取子串 $w[i:j]$ 时，两端都在子串内的配对保留，只剩一端的配对变成未配对；字母本身的类别始终保留。因此可以在原词的同一套位置、字母标签和配对关系上，检查一个任意子串是否满足减法规则。这正是嵌套词原文的子串约定。[Alur 与 Madhusudan，§2.2](https://www.cis.upenn.edu/~alur/Jacm09.pdf#page=8)

把 $0,1,\ldots,n$ 看作切点，$j$ 表示长度为 $j$ 的前缀。设 $\varphi_S$ 是识别规则语言 $S$ 的一元二阶逻辑（MSO）句子。将其每个位置量词限制到给定子串，字母和配对也限制到子串的真实字母位置，得到 $\varphi_S[i,j]$。切点 $j$ 可以一步走到 $i$，恰当且仅当 $i<j$ 且 $\varphi_S[i,j]$ 成立。

令 $X$ 是一个切点集合，同时要求

$$
\forall j\quad \bigl(j\in X\;\Longleftrightarrow\;
  \neg\exists i\,[i<j\ \land\ i\in X\ \land\ \varphi_S[i,j]]\bigr).
$$

先看 $j=0$，零切点没有更小的切点，因此空词必败且 $0\in X$。依次考察更大的 $j$，此前的切点已唯一确定是否属于 $X$，上式随之唯一确定 $j$。所以这个集合恰好记录了所有先手必败的前缀。输出句子对 $X$ 作一次存在量化，并要求最终切点 $n\in X$。对句子取否定即得必胜语言。在这一步即使输入规则允许空词，$i<j$ 也始终排除零长度的「一步」。

最后可消去辅助切点：对一个一阶变量分别考虑它等于初始切点或落在实际字母上的情形，对每个集合用一个布尔值记录是否包含初始切点。这样得到严格在原词 $1,\ldots,n$ 字母位置上解释的普通 MSO 句子。空词的位置域为空时，这个翻译也成立。有限嵌套词的 MSO 句子与嵌套词自动机等价；读可见标记的线性词时，后者又等价于可见下推自动机。[Alur 与 Madhusudan，Theorem 4.1 和 §5.1](https://www.cis.upenn.edu/~alur/Jacm09.pdf#page=25)

可见下推层级中的非正则现象确实会出现。例如取 $S=\{a^k b^k:k\ge1\}$。读 $a$ 入栈，读 $b$ 出栈，进入 $b$ 段后拒绝 $a$，恰好在读完一个非空匹配块时接受。对输入 $a^n b^m$，当 $0<m\le n$，唯一可删后缀是 $a^mb^m$，删除后只剩终局 $a^{n-m}$。当 $m>n$ 或 $m=0$，当前位置已经是终局。因此任意 $i<j$ 时，向 $a^i$ 和 $a^j$ 同时追加 $b^j$ 能区分其胜负。任何有限自动机都无法识别这里的胜态语言或败态语言。

## 在先结果与检索边界

- Fraenkel 研究了有限有向图的博弈核，其中无和棋部分的败态集合构成唯一的核。这是上述集合递推的已有理论出处。[Fraenkel 原论文，Theorems 5–6](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v4i2r10/pdf)
- Courcelle 与 Engelfriet 的反向翻译定理说明，MSO 可定义的结构解释保持目标属性的逆像可定义性。把固定词的切点解释成游戏图，并把“后缀是规则词”相对化成每对切点上的边谓词后，博弈核性质即可按此定理拉回到输入词。本文给出这项针对问题 4.1 的解释和可直接核查的公式。这些通用的逻辑方法与嵌套词的自动机对应已有文献。[Courcelle 与 Engelfriet，Theorem 1.40](https://www.labri.fr/perso/courcell/Book/TheBook.pdf#page=76) · [Alur 与 Madhusudan](https://www.cis.upenn.edu/~alur/Jacm09.pdf)
- 可见下推转导文献研究嵌套词上的 MSO 输入输出操作。Hague 与 Ong 的下推博弈胜区定理针对有限控制和局部栈顶改写所产生的配置图。一项由 VPL 识别的、可任意长的后缀删除，不是其定义中直接给出的栈顶改写规则。这里构造的是每个**有限输入词**上所有前缀的有向图，目标是识别输入词的语言。[两向可见下推转导原论文，§4](https://pageperso.lis-lab.fr/~pierre-alain.reynier/publis/lics16a.pdf) · [Hague 与 Ong，下推配置图和规则的定义](https://www.cs.ox.ac.uk/files/2278/Concur2009.pdf#page=3)
- 截至 2026 年 11 月 27 日，按作者、论文号、题号和 `word subtraction`、`suffix removal`、`visibly pushdown`、`nested words`、`monadic second-order`、`losing positions`、`game kernel` 的组合查找了公开论文、GitHub 代码和 Issues、TrureTuring、Ideosphere、EulerSolve。TrureTuring 的 GitHub issue 30286 明确讨论同一论文的问题 2.1，其预注册构造排除了该题作为本轮发现。AFTD 仓库已有该论文正常游戏定义和正则情形的状态构造。检索到的这些项目没有给出问题 4.1 的 VPL 闭包。在先一般定理已足以推出本文的逻辑路线。[TrureTuring 的问题 2.1](https://github.com/the-omega-institute/trureturing/issues/30286) · [AFTD 的原生胜态定义](https://github.com/rainwangphy/aftd-platform/blob/66c36a7654bde7e268444849e43d713ecdecc646/lean/AFTD/Kb/GameTheoryEconomics/WordSubtractionN.lean) · [AFTD 的正则规则状态](https://github.com/rainwangphy/aftd-platform/blob/66c36a7654bde7e268444849e43d713ecdecc646/lean/AFTD/Kb/GameTheoryEconomics/RegularWordSubtractionGameState.lean) · [Ideosphere](https://ideosphere.ai/explore) · [EulerSolve](https://eulersolve.org/papers/)
- MathDB 的公开索引按作者、题号、问题表述及等价术语检索，并检查了形式语言与减法博弈的公开标签目录。直接打开的原题页 374377 研究群上的 VPL 集合，363327 研究整数减法博弈的周期；两页的问题正文均不同于此处的词游戏。此次未定位到问题 4.1 自身可核实的 canonical 原题页，因此也没有该题正式解答区的读数。公开目录及按月订阅的完整 API 有不同覆盖范围。此次检索不能证明全网无人写过同样的论证。[MathDB 374377 原页](https://mathdb.com/p/374377/the-characterization-of-universally-quantified-visibly-pushd) · [MathDB 363327 原页](https://mathdb.com/p/363327/flammenkamp-s-conjecture-on-exponential-periods-in-subtracti) · [形式语言目录](https://mathdb.com/database?tag=formal-languages) · [减法博弈目录](https://mathdb.com/database?tag=subtraction-games) · [数据访问说明](https://mathdb.com/datasets)

## Lean 与独立复验

五个源文件按 `IntervalMSO.lean`、`SuffixGameMSO.lean`、`VisibleWords.lean`、`VisiblyPushdownSubtraction.lean`、`OrdinaryMSO.lean` 的次序编译。最后一份文件的主定理 `standardVPL_losing_positions` 和 `standardVPL_winning_positions` 采用通常的字母位置域，输入和输出使用相同的可见分类。`losingPosition_iff` 对应实际单步后缀删除，`holds_onFactor` 证明区间相对化，`losingSentence_correct` 证明败态集合唯一，`standardVPL_iff` 证明辅助切点不改变可定义语言。两个主定理仅依赖 Lean 的 `propext`、`Classical.choice`、`Quot.sound`。Lean 核验了输入句子到输出句子的全部变换，VPA 和 MSO 的经典双向等价引用上述 JACM 定理。

独立脚本 `check_finite.py` 穷举三字母表上长度 0 至 7 的全部 3,280 个词，对 105,796 个子串区间（含空区间）比较“重新用栈配对”和“裁剪整个输入的匹配关系”。它用三种规则分别按实际后缀删除计算胜负，再枚举所有切点子集核对逻辑公式的唯一解，共检查 9,840 次游戏结果。运行命令为 `python3 check_finite.py`。

## 在独立下载包中运行

本包锁定了 Lean 与 mathlib 版本。在本目录执行

```sh
lake exe cache get Mathlib.Data.List.OfFn Mathlib.Tactic.Push
lake build OrdinaryMSO
lake env lean -DwarningAsError=true OrdinaryMSO.lean
python3 check_finite.py
```
