# A121285 的四项递推

R. J. Mathar 于 2017 年为数列 A121285 提出一个含多项式系数的四项递推。Lean 已验证原条目列出的全部系数，以及所有可取下标 $n\ge3$。这个数列在正下标 $n$ 处计数尺寸为 $n+1$ 的对角对称凸 permutomino。Disanto 和 Rinaldi 在《Polyominoes determined by involutions》定理 4、公式 (9) 给出了计数闭式。此处对递推的证明以该闭式作为数列的定义。[Mathar 的原始递推](https://oeis.org/A121285) · [Disanto–Rinaldi 原论文](https://dmtcs.episciences.org/articles/3638/download)

令 $b_j=\binom{j}{\lfloor j/2\rfloor}$。对 $t\ge0$，闭式可写为

$$
a_{t+2}=(t+5)2^t-(t+2)b_{t+1}-(t+1)b_t,\qquad a_0=a_1=1.
$$

帕斯卡恒等式和相邻二项式系数的比值给出

$$
b_{2m+1}=\frac{2m+1}{m+1}b_{2m},\qquad b_{2m+2}=2b_{2m+1}.
$$

把闭式代入原递推。对 $n\ge5$，令 $t=n-5$。用上述两式按 $t$ 的奇偶性消去连续的五个二项式系数，只留下一个共同系数和 $2^t$。两者的系数在通分后都恒等于零。$n=3,4$ 直接代入初值成立。Lean 文件从标准库的二项式系数证明了两条相邻项关系，再把有理数域中验证的恒等式还原为整数等式。

截至 2026 年 11 月 27 日，按序列编号、原系数、作者、组合对象和数列前缀检索，未定位到这条具体递推的在先证明。原论文已经给出更早的闭式和生成函数，jOEIS 和 LODA 也已有可执行的闭式。形式化结果的范围是从已知闭式推出 Mathar 的递推。全球优先权无法通过公开检索确认。[jOEIS 实现](https://github.com/archmageirvine/joeis/blob/master/src/irvine/oeis/a121/A121285.java) · [LODA 实现](https://github.com/loda-lang/loda-programs/blob/main/oeis/121/A121285.asm)

在固定到 v4.24.0 的 Mathlib 环境运行 `lake env lean -DwarningAsError=true A121285.lean`。`Permutomino.mathar_recurrence` 的公理依赖为 `propext`、`Classical.choice`、`Quot.sound`。

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.Data.Nat.Choose.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
lake env lean -DwarningAsError=true A121285.lean
```
