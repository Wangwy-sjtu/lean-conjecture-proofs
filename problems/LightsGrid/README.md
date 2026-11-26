# Lights Out 有无穷多种边长的方盘恰有二维零空间

对每个正整数 $k$，边长 $n=2\cdot3^k-1$ 的标准 *Lights Out* 方盘恰有四种按灯后保持原灯态的按键图案，包括完全不按。也就是说，其按键矩阵在二元域 $\mathbb F_2$ 上的零空间维数恰为 2。前四个边长是 $5,17,53,161$。这证明了 William Boyles 的猜想 5.1，也给出了他在同一段落提出的具体无穷子族。[原论文，第 8 页](https://arxiv.org/pdf/2201.03452#page=8) · [作者猜想笔记](https://github.com/wmboyles/LightsOut-Math/blob/c730dfafc50c1e745d643654938d37851de8c06d/tex/conjectures/summary/conjectures.tex#L239)

一次按键翻转本格及上、下、左、右存在的邻格。给定任意可解初态，只要找到一个解，就可以把它与四种零空间图案分别作异或，得到全部四个解。实际求解时，在这族方盘上指定首行最左两个按键的取值，就唯一指定了一种零空间图案。[实际五格翻转和首行两位的线性同构](LightsGrid.lean)

## 四种图案

行列从 1 编号。令 $u_i$ 在 $i$ 为奇数时等于 1，其余为 0。令 $v_i$ 在 $3\nmid i$ 时等于 1，其余为 0。两个独立图案为 $u_i v_j$ 和 $v_i u_j$。空图案和这二者的逐格异或是另外两种。原因是路径邻接矩阵 $A$ 满足 $Au=0$、$Av=v$，而方盘的翻转算子由恒等、纵向邻接和横向邻接相加组成。两条数列在虚拟边界 $0,n+1$ 都取零。Boyles 已构造这两个方向上的零空间图案。下面证明任意 $k$ 时这两种模式都张成整个零空间。[Boyles 原文的偶覆盖构造](https://arxiv.org/pdf/2201.03452#page=3)

## 为什么没有第五种

定义二元域上的路径多项式 $F_0=0$、$F_1=1$、$F_{j+2}(X)=XF_{j+1}(X)+F_j(X)$。对 $N=2\cdot3^k$，有

$$\gcd(F_N(X),F_N(X+1))=X(X+1).$$

1. **排除三次幂阶的新根。** 写 $w(z)=z+z^{-1}$。特征二的域中若 $x^{3^j}=y^{3^j}=1$、$w(x)+w(y)=1$，则 $x,y$ 中至少有一个等于 1。为证此点，先看从 $3^{r+2}$ 降到 $3^{r+1}$ 的一步。令 $h=3^{r+1}$、$q=4^{3^r}$。二项式展开给出 $q=1+h(1+3t)$。对任意 $z^{3h}=1$，若 $z^h=1$，则 $z,z^q,z^{q^2}$ 三项之和为 $z$。若 $z^h$ 是非平凡三次单位根，三项之和为零。对 $z^{-1}$ 同样成立。这个求和算子具有加性并固定 1。若两个坐标都不在较低层，对原方程应用求和算子得到 $0=1$。若只有一个不在较低层，原方程结合求和后的方程使该坐标的 $w$ 值为零，因而该坐标为 1，也不可能。归纳归到三次单位根即可。[域上的完整证明](LightsTorsion.lean)
2. **得到多项式的最大公因式。** 在代数闭包内每个 $t$ 都能写为 $w(z)$，且 $w(z)F_j(w(z))=z^j+z^{-j}$。奇数下标处 $F_j(0)=1$。如果 $F_{3^k}(X)$ 与 $F_{3^k}(X+1)$ 有公共根，则能构造上一步排除的两个非平凡坐标。因此这两个多项式互素。利用 $F_{2j}(X)=XF_j(X)^2$ 和 Bézout 恒等式，$F_N(X)$ 与 $F_N(X+1)$ 的公共因子都整除 $X(X+1)$。直接在 0 和 1 取值可知这个二次式本身也是公共因子。[Lean 中的所有公共因子判据](LightsPolynomial.lean)
3. **回到真实方盘。** 任意零空间图案的第一行记为 $s$。从上边界逐行向下消去，底边界给出 $F_{n+1}(A+I)s=0$。路径两端的边界还给出 $F_{n+1}(A)s=0$。把第二步的 Bézout 等式代入 $A$，得到 $A(A+I)s=0$。于是 $s=As+(A+I)s$ 分解成两个路径特征向量，其特征值分别为 1 和 0。固定一个特征值后，第一个分量和左边界已通过二阶递推确定全行。特别地，若首行头两格都为零，这两个向量也都为零。再由逐行递推，整盘为零。前述两种显式图案在头两格上线性独立，遂得到所需线性同构。[Lean 对每格按键和零空间维数的证明](LightsGrid.lean)

## 公开先例

Sutner 的工作及 Muñoz 的定理 1 已把一般方盘的零空间维数写成路径多项式最大公因式的次数。Hunziker、Machiavelo、Park 研究了有限域上的路径多项式和网格可逆性。Zaidenberg 的定理 0.2 给出二元谱曲线的单位根参数表示。这里在该曲线上逐层排除了新的三次幂阶坐标，并在形式证明中从真实五格翻转重新推导了到方盘的联系。[Muñoz 的定理 1 与 3](https://www.mat.ucm.es/~vmunozve/lights-out.pdf) · [Hunziker 等](https://doi.org/10.1016/j.tcs.2004.03.031) · [Zaidenberg 的谱曲线](https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2006/14.pdf#page=3)

截至 2026-11-27，检索使用论文名、题号、arXiv 编号、nullity two、three-power torsion、partner orders 以及幂次族的不同写法。作者公开仓库把上述公式列作猜想。GitHub 中另一个公开数学项目实现了普通 Lights Out 消去算法。其目录未给出三次幂族结果。另检查了公开 GitHub 讨论、TrureTuring、可索引的 MathDB 资料和 Hexagon 站内检索。所查资料中未找到这个猜想的在先完整证明。Boyles 已在同一论文定理 4.2 证明“零度为二必有 $n\equiv-1\bmod6$”；本条解决的是第 5 节提出的无穷性。[作者原文](https://arxiv.org/pdf/2201.03452#page=7) · [公开算法记录](https://github.com/CylicAmp/CylicAmp/blob/2a955686cf4ee4fbd83567fae0c6af2af7a49237/math/theorems/lights_out_gf2_gf37.py) · [OpenAlex 预印本记录](https://openalex.org/W4225106851)

## 复验

项目固定 Lean 4.24.0 和 mathlib 版本。从本目录运行

```sh
lake exe cache get Mathlib.Algebra.CharP.Two Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.Algebra.Polynomial.FieldDivision Mathlib.Data.ZMod.Basic Mathlib.Algebra.Field.ZMod Mathlib.LinearAlgebra.Dimension.Constructions Mathlib.Order.Preorder.Finite
lake build LightsTorsion LightsPolynomial
lake env lean -DwarningAsError=true LightsTorsion.lean
lake env lean -DwarningAsError=true LightsPolynomial.lean
lake env lean -DwarningAsError=true LightsGrid.lean
python3 check_lights.py
```

独立程序对边长 $1$ 到 $20$ 以及 $53$ 的真实翻转矩阵做二元高斯消元，并在 $1$ 到 $54$ 上对比逐行消去与多项式方法。另逐项验证了 $k=1,\ldots,9$ 的精确最大公因式，最大边长为 $39{,}365$。Lean 的无穷性定理为 `LightsGrid.infinitely_many_nullity_two`；其公理依赖仅有 `propext`、`Classical.choice` 和 `Quot.sound`。[独立复核程序](check_lights.py)
