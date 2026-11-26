# 奇数底数幂次方盘的稳定性 · 已有结果的 Lean 形式化

令 $d(n)$ 为边长 $n$ 的标准 Lights Out 方盘的零空间维数。按键图案在二元域上相加，边界外视为零。因此 $d(n)$ 是描述全部不改变灯态的按键图案所需的独立比特数。取空盘 $d(0)=0$。

Boyles 在公开猜想笔记中写下了三个量词不同的问题。对不能被 21 整除的奇数 $a$，他猜测 $d(a^k-1)$ 总等于 $d(a-1)$。随后他猜想对每个奇数 $a$ 总会最终稳定，并推测第二个指数足以作为所有底数的起点。[作者原笔记，第 222–232 行](https://github.com/wmboyles/LightsOut-Math/blob/c730dfafc50c1e745d643654938d37851de8c06d/tex/conjectures/summary/conjectures.tex#L222-L232)

作者后来的公开非默认分支已经解决上述问题。其 AI 稿还证明了对任意有限组奇素因子逐个截断指数的更一般结论，给出底数 57 的全部数值，并为每个指定指数 $K\ge3$ 构造恰在 $K$ 稳定的底数。本目录给出可机检的另一种下降和跳变构造。[在先稿，定理和例子](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/multiprime_stabilization/multiprime_stabilization.tex) · [AI 文稿说明](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/README.md)

## 所有奇数底数的精确约化

任取正奇数 $a$。取任何满足 $a\mid 2^e-1$ 的正整数 $e$，记 $c=2^e-1$。则对所有整数 $k\ge0$，

$$
d(a^k-1)=d\bigl(\gcd(a^k,c)-1\bigr).
$$

特别地，$d(a^k-1)$ 对每个固定的 $a$ 最终保持常数。可取 $e=\varphi(a)$。右边的下标只取决于 $c$ 的有限多个因子，且 $\gcd(a^k,c)$ 按整除关系单调上升。这给出了有限计算方法。[精确约化和最终稳定定理](OddStabilization.lean)

对 $a=57$，取 $e=18$。当 $k=1,2,3$ 时，相应的最大公因数是 57、171、513，随后一直为 513。结果为

| 指数 $k$ | 边长 $57^k-1$ | $d(57^k-1)$ |
| --- | ---: | ---: |
| 1 | 56 | 0 |
| 2 | 3,248 | 36 |
| 3 | 185,192 | 252 |
| 每个 $k\ge 3$ | $57^k-1$ | 252 |

由于 $21\nmid57$，这一底数同时否定了立即稳定和统一从指数 2 开始稳定的猜测。三个有限次数使用 Lean 内核验证的二元多项式消去求得。更大的全部指数由一般定理和整数整除关系覆盖。[完整幂次列与两个反例定理](OddGridExamples.lean)

## 为什么更高幂不会一直增加零空间

用 $F_0=0,F_1=1,F_{i+2}(X)=XF_{i+1}(X)+F_i(X)$ 表示路径多项式。方盘的两个边界条件给出 $d(N-1)=\deg\gcd(F_N(X),F_N(X+1))$。这是已有的方盘公式。Lean 中从五格翻转规则重新构造了线性同构，把实际零空间与 $\mathbb F_2[X]/(g)$ 的对偶空间对应起来，其中 $g$ 是两个边界多项式的最大公因式。[一般方盘的形式证明](GridGcd.lean) · [Muñoz 的定理 1](https://www.mat.ucm.es/~vmunozve/lights-out.pdf)

1. 写 $w(x)=x+x^{-1}$。奇数 $N$ 时，两个边界多项式的公共根 $t$ 给出曲线 $w(x)+w(y)=1$ 上的点，其中 $x,y\ne1$，$w(x)=t$，$w(y)=t+1$，且 $x^N=y^N=1$。这用到恒等式 $w(x)F_N(w(x))=x^N+x^{-N}$。[路径多项式与单位根](LightsPolynomial.lean) · [Zaidenberg 的谱曲线](https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2006/14.pdf#page=3)
2. 置 $q=2^e$，$q_j=q^{a^j}$，$c_j=q_j-1$。若 $a\mid c_j$，二项式展开给出 $c_{j+1}=a c_j(1+c_j u_j)$，括号内因子与 $a$ 互素。于是 $a^j\mid c_j$。对 $a$ 幂阶的曲线坐标，从 $z^{c_{j+1}}=1$ 可先约去互素因子，得到 $z^{a c_j}=1$。令 $h=z^{c_j}$，它满足 $h^a=h^{c_j}=1$。求和算子 $L(z)=\sum_{i=0}^{a-1}z^{q_j^i}=z\sum_{i=0}^{a-1}h^i$ 在 $h=1$ 时保留 $z$，在 $h\ne1$ 时将它变为零。$L$ 可加，由于 $a$ 奇，它固定 1。坐标与其逆元总是同时保留或同时变为零。对曲线方程施加 $L$，两坐标都消失会给出 $0=1$，只消失一个则该坐标的 $w$ 值必为零，故坐标等于 1。由此逐层下降，得到 $x^c=y^c=1$。[对任意奇数底数的域上下降](OddTorsion.lean)
3. 令 $m=\gcd(a^k,c)$，$n=a^k/m$。两个坐标的阶都整除 $m$，因此高下标的每个公共根也出现在下标 $m$。重数由恒等式 $F_{mn}(T)=F_m(T)F_n(TF_m(T))$ 控制。在 $F_m(T)=0$ 处，第二因子的值总是 $F_n(0)=1$。因此沿两个方向增加的因子分别与另一方向的高下标多项式互素。两个最大公因式相伴，次数相等。这一步保留了因子重数。[多项式恒等式与重数推导](OddStabilization.lean)


## 任意晚的严格跳变

给定任何正整数 $s$，总存在一个正奇数 $a$，使 $d(a^s-1)<d(a^{s+1}-1)$。所以每个底数各自最终稳定，但没有一个起始指数适用所有底数。[任意指定指数的严格跳变](LateJumps.lean)

一个显式构造如下。令 $r=3^{s+1}$、$q=4^{3^s}$。逐次立方得 $q=1+rb$ 且 $b\equiv1\pmod 3$。令 $c=b(q+1)$、$a=3c$，则 $c$ 与 3 互素且 $a$ 为奇数。因此 $r\nmid a^s$，而 $q^2-1=rc$ 整除 $a^{s+1}$。

在二元域的代数闭包里取一个恰有阶 $r$ 的单位根 $x$，令 $t=x+x^{-1}$。因 $r\ge9$，这个 $t$ 既不是 0 也不是 1。取非零 $y$ 使 $y+y^{-1}=t+1$。由 $r\mid q-1$ 有 $x^q=x$，故 $y^q$ 与 $y$ 具有相同的 $w$ 值。方程 $w(z)=w(y)$ 的两个根为 $y,y^{-1}$，所以 $y^{q^2}=y$。现在 $x,y$ 的阶均整除 $a^{s+1}$，使 $t$ 成为高下标的公共谱根。低下标没有这个根，因为它将迫使 $x^{a^s}=1$。低下标的最大公因式整除高下标的最大公因式，新增的根便迫使其次数严格增大。


## 公开记录与优先权

Brouwer 的表早已将 171 列为能产生非零零空间的最小整除下标之一。57 本身未列在小于 171 的完整小例中。结合下标倍数的性质，已有数据足以得出第一次跳变的定性结论。Muñoz 的次数九因子记录也已经给出周期 513。这里逐一核验这两个已有线索，对同一底数给出了全部指数的精确零空间维数及所有奇数底数的稳定性证明。[Brouwer 的表](https://aeb.win.tue.nl/ca/madness/mad1.html) · [Muñoz 的周期与因子表](https://www.mat.ucm.es/~vmunozve/lights-out.pdf)

Zaidenberg–Zagier 证明了搭档图的各连通分支有限。Boyles 仓库中的有限支撑稳定定理，以及底数 57 与任意晚稳定两个结果，都已有完整的公开证明。旧版查重漏掉了非默认分支，此处更正。我们的全称量词、实际网格与有限算术均由 Lean 检查。[搭档图定理 3.11](https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2006/14.pdf#page=22) · [作者仓库的直接先例](https://github.com/wmboyles/LightsOut-Math/blob/e1b2f18988467dd552727fab8dbd039f1639f6a3/tex/ai_gen/multiprime_stabilization/multiprime_stabilization.tex)
