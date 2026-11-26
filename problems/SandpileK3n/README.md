# 完全二部图 $K_{3,n}$ 的随机沙堆缺额多项式

**定理。** 对每个 $n\ge2$，取完全二部图 $K_{3,n}$，令吸收点位于三个顶点的一侧。按总缺额 $k$ 统计随机常返稳定配置，所得系数 $L_0,\ldots,L_{2n-2}$ 全部为正，满足

$$L_{k+1}^2\ge L_kL_{k+2}\qquad(0\le k\le 2n-4).$$

因此这些系数存在一个峰值，峰前不降、峰后不升。Alofi 和 Dukes 在 *Discrete Mathematics* 348 (2025), 114323 的猜想 13(i)、(ii) 对所有 $K_{m,n}$ 提出这两条性质。他们证明了 $m=2$ 和 $n=2$，并给出 $m+n\le8$ 的计算表。这里证明 $m=3$ 的整行，包括超出该表的全部 $n\ge6$。更大的 $m$ 和交换吸收点所在一侧后的 $K_{n,3}$ 仍需分别研究。[期刊论文](https://doi.org/10.1016/j.disc.2024.114323) · [原文猜想 13 与表 2](https://arxiv.org/html/2411.02667v1#S3)

## 模型和计数公式

一个稳定配置给每个非吸收顶点 $v$ 分配 $c(v)\in\{0,\ldots,d(v)-1\}$ 颗沙粒，其中 $d(v)$ 是顶点度数。缺额为 $d(v)-1-c(v)$，即相对于可以稳定容纳的最多沙粒数，还差几颗。Chan、Marckert 和 Selig 的定理 3.2 给出从随机动力学到定向图的桥梁。配置随机常返当且仅当各边存在一种定向，使每个非吸收顶点的入度至少为其缺额加一。形式化从 Alofi–Dukes 命题 4 重述的这条已发表等价刻画开始。[定向判据](https://arxiv.org/html/2411.02667v1#S1) · [Chan–Marckert–Selig](https://www.labri.fr/perso/marckert/SP.pdf)

用 $u,v$ 表示左侧两个非吸收顶点的缺额，右侧 $n$ 个带标号顶点的缺额排成字 $w\in\{0,1,2\}^n$。记 $z$ 为字中 2 的个数，$t$ 为非零位数，$R=t+z$ 为右侧总缺额。存在兼容定向当且仅当

$$u+z<n,\qquad v+z<n,\qquad u+v+R\le 2n-2.$$

可以把吸收点的边全都指向右侧。每个 2 还需要两个非吸收的左顶点各提供一条入边，每个 1 还需要这两个顶点合计提供一条。左侧两顶点最多分别能提供 $n-1-u,n-1-v$ 条，三个不等式正好保证足以先分配所有的 2，再分配所有的 1。Lean 枚举时允许吸收点边的两个方向，并从这一完整模型证明上述充要条件。

设 $D=2n-2$，$0\le k\le D$。固定 $w$，有 $u+v=k-R$ 且 $0\le u,v<n-z$。不加上界时共有 $(k+1-R)_+$ 对，记 $a_+=\max(a,0)$。分别剔除 $u$ 或 $v$ 达到上界的情况。两者同时越界至少需要总缺额 $R+2(n-z)\ge2n$。因此每个字贡献

$$ (k+1-R)_+ -2(k+1-n-t)_+.$$

令 $A_k=[x^k](1+x+x^2)^n$，$B_k=[x^k]x^n(1+2x)^n$。对所有带标号的字求和得到

$$ L_k=\sum_{i=0}^k(k-i+1)(A_i-2B_i),\qquad 0\le k\le D.$$

等价地，$L_{3,n}(x)$ 等于 $\big((1+x+x^2)^n-2x^n(1+2x)^n\big)/(1-x)^2$ 在 $x=0$ 处幂级数展开至 $D$ 次的截断。每个次数都在支撑内，因为取 $w$ 全为零后，$u,v\in\{0,\dots,n-1\}$ 的和可以达到 $0$ 至 $D$ 的每个整数。

## 对数凹性

三项式系数 $A_k$ 在 $0\le k\le2n$ 上为正、对称且对数凹。对数凹性可逐次与 $(1,1,1)$ 卷积证明。给和为 $s$ 的字标记一个零，再把标记改成 1。原字至少有 $n-s$ 个零，所得字至多有 $s+1$ 个 1，故 $(n-s)A_s\le(s+1)A_{s+1}$。由对称性，取 $k=n+j$ 得 $(j+1)A_{k+1}\le(n-j)A_k$。另一方面，二项式递推给出 $(j+1)B_{k+1}=2(n-j)B_k$。

写 $q_k=B_k/A_k$。上述不等式推出 $q_{k+1}\ge2q_k$；当 $k<n$ 时 $B_k=0$，结论同样成立。因此 $q_k$ 非负、非减且离散凸。令 $C_k=A_k-2B_k=A_k(1-2q_k)$。$C_k$ 的正项形成一个前缀，在这个前缀上 $1-2q_k$ 是正的凹序列，因而对数凹。它与 $A_k$ 的逐项乘积 $C_k$ 也对数凹。

若 $C_{k+2}>0$，从零到 $k+2$ 的 $C_i$ 全部为正且对数凹。正的对数凹序列取前缀和后仍对数凹，计数公式中连续取两次前缀和，得到 $L_{k+1}^2\ge L_kL_{k+2}$。若 $C_{k+2}\le0$，计数公式直接给出 $L_{k+2}-2L_{k+1}+L_k=C_{k+2}\le0$。此时算术平均数与几何平均数不等式给出同一结论。由于整段 $L_k$ 都为正，一旦系数开始下降，之后便不可能重新上升，于是得到单峰性。

## 核验

`SandpileK3n.lean` 使用 Lean 4.24.0 和 mathlib v4.24.0。解压后可在本目录按文末的命令复验。

| Lean 声明 | 核验内容 |
| --- | --- |
| `compatible_iff` | 完整逐边定向与三个不等式双向等价 |
| `mem_recurrentConfigs`、`recurrentConfigs_nodup` | 枚举恰好包含总缺额为 $k$ 的全部兼容配置，且每个只出现一次 |
| `length_recurrentConfigs`、`coefficient_count` | 此枚举的长度等于显式计数，并等于差序列的二重前缀和 |
| `lackCount_pos` | $0,\ldots,2n-2$ 均有配置 |
| `alofi_dukes_configurations` | 直接对该配置列表的长度证明全部对数凹不等式和单峰性 |

[lean-check.txt](lean-check.txt) 是七项声明的 Lean 公理报告，仅列出 `propext`、`Classical.choice`、`Quot.sound`。另可用 Python 3.10 及以上运行 `python3 check_examples.py`。它对 $n=2,\ldots,6$ 逐一考虑每条边的定向以及兼容配置，用集合去重，再与系数公式独立比较。$n=5$ 时峰值为 $610$，最后一项降至 $585$，与论文表 2 一致。下一个规模 $n=6$ 给出

$$ 1,8,36,114,282,576,1009,1544,2049,2284,2060. $$

## 在先结果核查

截至 2026 年 11 月 27 日，按论文题名、作者、编号 `2411.02667`、`lacking polynomial`、`stochastically recurrent`、`log-concave`、带标号 $K_{3,n}$、低阶系数、三项式及二项式公式检索期刊、arXiv、GitHub 代码和 Issues、TrureTuring。以下结果与本题最接近。检索覆盖公开可索引的记录，优先权仍可随新增材料修正。

- Selig 和 Zhu 的定理 2.1 给出一般完全二部图的常返性子集判据，定理 2.2 进一步缩小需要检查的不等式。他们将包含吸收点的这一侧记作 $m+1$ 个顶点。该文可作为本文兼容性分析的既有起点，研究重点为常返性判定、燃烧算法与 Ferrers 图。[Selig–Zhu 原文](https://arxiv.org/html/2409.11811v1#S2)
- TrureTuring 已回答 Alofi–Dukes 的**问题 6**，即常返配置占所有稳定配置的比例是否超过一半。对其代码库检索 `lacking polynomial` 命中论文资料和这项比例证明。本文所证的猜想 13 关乎各缺额层之间的系数关系。[TrureTuring 问题 6 的记录](https://github.com/the-omega-institute/trureturing/blob/f715de7e90b4cb54961c6b14f514428f8e73fb88/Blueprint/D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.md)
- GitHub 全站代码检索 `"lacking polynomial" "log-concavity"` 的相关命中转载了原论文摘要。在 `1337isnot1337/solved-conjectures` 的代码和 Issues 中，以题名关键词、作者名及 arXiv 编号检索亦未找到这个无限族的证明。[摘要转载](https://github.com/ehijano/rss_fetch/blob/2820b6d225aac11cdc3f9e8f0136ff031869cee9/rss_data/math.CO/2024-11-06_math.CO.xml) · [公开问题库](https://github.com/1337isnot1337/solved-conjectures)
- Giansiracusa、Rincón、Schleis 和 Ulirsch 的定理 B 给出离散多拟阵的对数凹计数，其中每个向量 $\alpha$ 的权重含 $1/\prod_i\alpha_i!$。缺额多项式要求每个配置恰计一次；本证明直接处理这种普通计数。[定理 B](https://arxiv.org/html/2407.05808v1#S0)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.Nat.Choose.Basic Mathlib.Algebra.BigOperators.Ring.List Mathlib.Data.List.Nodup Mathlib.Order.Interval.Finset.Nat Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring Mathlib.Tactic.Positivity.Basic Mathlib.Tactic.FieldSimp
lake env lean -DwarningAsError=true SandpileK3n.lean
```

另核查 TrureTuring 网站的已解目录快照。同一论文号在该目录中对应随机常返配置是否占半数的问题 6。[已解目录的固定快照](https://github.com/the-omega-institute/trureturing-pages/blob/5665185be1a26a75882c20f89683256c9a4bbfd3/site/assets/open-math/problem-resolutions.json)
