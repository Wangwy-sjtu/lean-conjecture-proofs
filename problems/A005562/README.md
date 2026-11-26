# 象限格点游走的固定高度递推

一颗粒子从正方格点原点出发，每一步任选东、西、南、北之一，经过的坐标始终满足 `x ≥ 0`、`y ≥ 0`。令 $W_{n,y}$ 是走 $n$ 步后恰好停在高度 $y$ 的路径条数，横坐标任意。如果四个方向各以 $1/4$ 的概率选择，则 $W_{n,y}/4^n$ 也是粒子一直留在象限内并以高度 $y$ 结束的概率。

R. J. Mathar 于 2017 年 4 月 2 日在 OEIS 多个固定高度的条目中写下二阶递推猜想。以下单个等式对所有整数 $y\ge0$、$n\ge y+2$ 成立。这里的下界确保三个计数都落在相应 OEIS 列的定义域内。[高度 0](https://oeis.org/A005558) · [高度 1](https://oeis.org/A005559) · [高度 2](https://oeis.org/A005560) · [高度 3](https://oeis.org/A005561) · [高度 4](https://oeis.org/A005562)

$$
\begin{aligned}
&(n-y+1)(n-y)(2n+1)(n+y+3)(n+y+2)W_{n,y} \\
&\quad=4n(n+1)(2n^2+4n+2y^2+4y+3)W_{n-1,y}\\
&\qquad+16n^2(n-1)(2n+3)(n+1)W_{n-2,y}.
\end{aligned}
$$

例如取 $y=4$，系数中的 $2y^2+4y+3$ 变为 $51$，左边出现 $(n-3)(n-4)(2n+1)(n+7)(n+6)$，恰是原条目的公式。取 $y=1$ 时可约去公因子 $n$，取 $y=0$ 时可约去 $n(n+1)$。高度 0 的条目还列出三阶递推，这里只处理上述二阶族。[Mathar 的原猜想](https://oeis.org/A005562)

## 从路径到递推

令 $L_n(t)$ 表示一维无约束的 $n$ 步游走从 0 到 $t$ 的方案数。若 $n-t$ 为偶数，则 $L_n(t)=\binom n{(n-t)/2}$，越界的二项式系数取零。当奇偶性不符时也取零。换到坐标 $(x+y,x-y)$ 后，每个平面步恰对应一对独立的正负步。因此不加边界的端点计数是 $U_n(x,y)=L_n(x+y)L_n(x-y)$。

对象限边界各作一次反射，所得端点计数是 $U_n(x,y)-U_n(x+2,y)-U_n(x,y+2)+U_n(x+2,y+2)$。形式证明从四个末步的递推验证这一式子，并在边界 $x=-1$、$y=-1$ 验证消去。对横坐标求和只剩下 $x=0,1$ 的四项。这也从实际步词重新证明了 Guy 第 4 节图 5 下的二项式公式。[Guy，2000](https://cs.uwaterloo.ca/journals/JIS/VOL3/GUY/catwalks.html)

为了得到统一递推，固定 $y,k\ge0$，记 $s=y+2k$。用阶乘化简相邻计数可得

$$
\frac{W_{s+1,y}}{W_{s,y}}=\frac{(s+2)(s+1)}{(k+1)(y+k+2)},\qquad
\frac{W_{s+2,y}}{W_{s+1,y}}=\frac{(s+3)(s+2)}{(k+1)(y+k+2)}.
$$

按 $n-y$ 的奇偶取相邻两次过渡，代入后两种情形满足同一个多项式等式，即上述二阶递推。这里可以用交叉相乘的等式完成推导，Lean 仅以已证正的阶乘与正整数作除数。

## Lean 核验

[A005562.lean](./A005562.lean) 中的 `QuadrantWalks.paths` 枚举实际四方向步词，按从终点到起点的次序存储。定理 `paths_nodup` 证明同一词不会重复，`no_paths_past` 证明不可达的横坐标没有遗漏的路径。自然数值 `walkCount` 计算各合法末点的词数。定理 `walk_eq_count` 把它与 Guy 的闭式连接。主定理 `quadrant_walk_recurrence` 直接以 `walkCount` 陈述自然数等式。

使用 Lean 4.24.0 和 mathlib v4.24.0，在已有对应 mathlib 的 Lake 项目内运行

```sh
lake env lean -DwarningAsError=true A005562.lean
```

文件自带三个 `#print axioms` 命令。运行上述命令会输出 `mathar_recurrence`、`walk_eq_count`、`quadrant_walk_recurrence` 的公理依赖，本次检查三项均为 `propext`、`Classical.choice` 和 `Quot.sound`。

## 与已有结果的关系

截至 2026-11-27，在下列可检索来源中未找到同一条任意高度二阶式的已有证明。格路计数本身、其闭式和生成函数均有充分前史。这里的贡献是写出统一递推，以及从有限步词到该递推的端到端形式证明。未公开或未被索引的解答无法从检索结果排除。

| 来源 | 核查结果 |
| --- | --- |
| OEIS 与原文 | Guy 在 2000 年发表任意高度的二项式公式。A052174 重述该式，并于 2026 年增列以 Bessel 函数表示的各列指数生成函数。A005558 至 A005562 的二阶公式仍标为 Mathar 猜想。[原论文第 4 节](https://cs.uwaterloo.ca/journals/JIS/VOL3/GUY/catwalks.html) · [A052174](https://oeis.org/A052174) |
| arXiv 与作者提供的计算结果 | Bousquet-Mélou 给出固定二维末点计数的超几何公式。Bostan 等人给出小步模型的完全生成函数 $Q(u,v;t)$，并证明 $Q(1,0;t)$ 等特化的微分方程。固定任意高度所求的列是 $[v^y]Q(1,v;t)$。在其论文和配套公式表中未找到这条以 $y$ 为参数的系数递推。[Bousquet-Mélou](https://arxiv.org/abs/1511.02111) · [Bostan 等人](https://arxiv.org/abs/1606.02982) · [配套公式表](https://specfun.inria.fr/chyzak/ssw/closed_forms.html) |
| GitHub Code 与公开 Issues | 用编号 A005562、A052174、多个高度的编号组合及系数片段 `2*n^2+4*n+51` 查找。直接核对的 jOEIS 程序用二项式之差，LODA 程序用二项式之积，二者计算固定高度 4。精确系数的命中是 OEIS 的镜像。A005562、A052174 的公开 Issues 查询无命中。指定 Google DeepMind 的 formal-conjectures 检索 A005562、指定 mathlib4 检索 A052174 也无命中。[jOEIS](https://github.com/archmageirvine/joeis/blob/18a7aeb71b9c17d6262be076b0a621cdcf6e76e4/src/irvine/oeis/a005/A005562.java) · [LODA](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/005/A005562.asm) |
| 公开解题平台 | 以编号、原系数、Guy 固定高度、首象限核方程、holonomic recurrence 等关键词检索，并查找公开 AI 解题记录。TrureTuring 返回一则题名相似的 Mathar 证明，其对象是一维半直线上从高度 3 出发的存活路径，满足三阶递推。[该公开解答](https://www.trureturing.org/knowledge/node/98f5aa0db65faf6c355712db98a3067d217771be6fd8069e97d0e59aec17f9b1/) |

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Data.List.Nodup Mathlib.Data.Nat.Choose.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Positivity.Basic Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true A005562.lean
```
