# A001122 的一个原根反例

Thomas Ordowski 在 2023 年 11 月 27 日给 OEIS A001122 写下一个观察。如果 $k\ne2$，且 $2^k+3$ 为素数，那么 2 似乎总是它的原根。取 **$k=2191$** 即可证伪。指数 2191 已出现在 OEIS A057732 的已知数列中。本次检验的是底数 2 的原根性质。[原猜想](https://oeis.org/A001122) · [已知指数](https://oeis.org/A057732)

令 $p=2^{2191}+3$，它有 660 位十进制数字。Lean 证明了 $p$ 是素数，$5\mid p-1$，并且

$$
2^{(p-1)/5}\equiv 1\pmod p.
$$

模 $p$ 的乘法阶是使 $2^d\equiv1\pmod p$ 的最小正整数 $d$。上式给出 $d\le(p-1)/5<p-1$，而原根的阶必须等于 $p-1$。因此这个数就是一个反例。

## 如何复验

在 Lean 和 mathlib 均为 v4.24.0 的项目中执行下列命令。所有计算都由 Lean 内核核对，复验无需连接数论数据库。

```sh
lake env lean A001122.lean
```

[证明源文件](./A001122.lean) 中的 `prime_N` 证明素性，`five_divides` 和 `fifth_power_test` 证明整除性及模幂等式，`ordowski_second_claim_false` 是对原全称命题的否定。上述复验返回码为 0。文件打印了素性、模幂及最终定理的公理依赖，三项均为 `propext`、`Classical.choice` 和 `Quot.sound`。

## 素性证书

从 $p-1=2(2^{2190}+1)$ 的部分分解中选出四个素因子，它们的乘积 $F$ 有 243 位。文件提供具体底数 $b$。对每个列出的素因子 $q\mid F$，Lean 验证

$$
b^{F}\equiv1\pmod p,\qquad \gcd(b^{F/q}-1,p)=1.
$$

第二个等式在代码中使用模 $p$ 的小余数计算。对 $p$ 的任意素因子 $r$，这两项保证 $b$ 模 $r$ 的阶恰为 $F$，从而 $F\mid r-1$。这些判断对尚在检验的 $p$ 也成立。[公开因子数据](https://factordb.com/index.php?id=1000000000012152214)

若 $p$ 是合数，取一个真素因子。因为 $p\equiv1\pmod F$，相应的余因子也模 $F$ 余 1。于是可写 $p=(uF+1)(vF+1)$，其中 $u,v\ge1$。设 $T=(p-1)/F=Fuv+u+v$。由 $u+v\le uv+1$ 得

$$
T\bmod F\le u+v\le uv+1\le\lfloor T/F\rfloor+1.
$$

本例中左边有 241 位十进制数字，$\lfloor T/F\rfloor$ 有 176 位。Lean 直接检验反方向的严格不等式，排除了这种分解。代码用同样的判据或平方根界递归认证所需的较小素因子，合计 23 个证书节点。数据库提供的数字只作为待验输入。

## 公开记录

截至 2026 年 11 月 27 日，按两条数列编号、作者、原句、相关的乘法阶表述和具体指数检索 OEIS、公开网页以及可索引的论文或代码结果，未检出已发表的同一原根反例。A001122 在 2026 年 11 月 3 日登记的 $p=643$ 反例，由 Alper Ferudun 针对 Ordowski 同一段落中的第一项猜想给出。本文件检验的是该段落的第二项。公开检索的覆盖范围有限，首次发现的优先权未独立确立。[OEIS 完整评论](https://oeis.org/A001122/internal)

## 在独立下载包中运行

本目录已锁定版本。从该目录执行

```sh
lake exe cache get Mathlib.NumberTheory.LucasPrimality Mathlib.Tactic.NormNum.Prime
lake env lean -DwarningAsError=true A001122.lean
```
