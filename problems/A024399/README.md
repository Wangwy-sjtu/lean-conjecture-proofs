# A024399 的七阶递推与生成函数

**结论**　R. J. Mathar 于 2011 年 10 月 8 日给出的递推对所有原条目下标都成立。Lean 也逐系数验证了相应的普通生成函数。[原始条目](https://oeis.org/A024399)

## 命题

对正整数 $n$，取 $S_n=\{2,5,8,\ldots,3n+5\}$，它有 $n+2$ 个元素。记 $e_1$ 为元素之和，$e_3$ 为对所有三元子集的元素乘积求和，令 $a_n=\lfloor e_3/e_1\rfloor$。例如，$n=1$ 时 $a_1=\lfloor80/15\rfloor=5$。

对 $n\ge1$ 有

$$
a_{n+7}=4a_{n+6}-6a_{n+5}+5a_{n+4}-5a_{n+3}+6a_{n+2}-4a_{n+1}+a_n.
$$

## 证明

将一个新元素 $v$ 加入集合时，$e_j$ 变为 $e_j+v e_{j-1}$。对集合长度归纳得到

$$
e_1=\frac{(n+2)(3n+7)}2,\qquad
e_3=\frac{n(n+1)(n+2)(3n+7)(9n^2+33n+22)}{48}.
$$

因此 $24e_3/e_1=P(n)=n(n+1)(9n^2+33n+22)$。把 $n$ 按模 24 分类，可见 $P(n)$ 除以 24 的余数在 $n\equiv1\pmod 3$ 时为 8，其余为 0。这个余数函数 $r(n)$ 以 3 为周期，且 $24a_n=P(n)-r(n)$。

记 $E$ 为向前移一项的算子。$E^3-1$ 消去 $r$，并把四次多项式 $P$ 变成至多三次的多项式。再取四次有限差分，可得 $(E-1)^4(E^3-1)a=0$。展开即为上述递推。将初值代入，所得生成函数为

$$
\sum_{n\ge1} a_nx^n=\frac{x(5+11x+7x^2+5x^3-x^4)}{(1+x+x^2)(1-x)^5}.
$$

## Lean 复验

在本目录使用 Lean 4.24.0 标准发行版运行

```sh
lean A024399.lean
```

源码从基本对称函数的子集递归定义出发，将 $a_0$ 自然延拓为 0。七阶递推由 `A024399.mathar_recurrence` 证明，生成函数乘以其分母后的每个系数由 `A024399.generating_function_coefficients` 验证。两者的 `#print axioms` 均只列出 `propext`、`Classical.choice` 和 `Quot.sound`。[Lean 源码](A024399.lean)

## 已有工作与检索

2026 年 11 月 27 日按编号、首项、递推系数和对称函数定义检索了 OEIS、LODA 及公开证明库。A024392 已给出分子闭式，LODA 在 2025 年已有递推程序和模 3 分类程序。检索未发现对 A024399 这条递推从原定义出发的公开证明文本。此处补充可执行的形式证明，已有公式及程序的出处见下。[分子闭式](https://oeis.org/A024392) · [LODA 递推程序](https://github.com/loda-lang/loda-programs/blob/537ce9a79f9f/oeis/024/A024399.asm) · [LODA 模 3 程序](https://github.com/loda-lang/loda-programs/blob/9e53ab89093a/oeis/024/A024399.asm)
