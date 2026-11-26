# 十进制旋转相加不能连续五次保持素性

Chuck Seggelin 于 2003 年提出猜想。若十进制表示有偶数位，交换左右两半。若有奇数位，交换等长的左右两块，把中央一位留在原处。令 $T(n)$ 等于原数加旋转后的数。每一步按新数的实际位数重新分块。已验证的结论是，对任意自然数 $p$，$p,T(p),\ldots,T^5(p)$ 中至少有一个不是素数。[旋转的定义](https://oeis.org/A086002) · [猜想 2](https://oeis.org/A086004)

## 证明

1. 偶数位的素数无法在下一步保持素性。把数写作 $aM+b$，其中 $M=10^m$ 是半段的位权。相加得到 $(M+1)(a+b)$。若 $a+b=1$，原数只能是 $1$ 或 $M$，均不符合偶数位素数的假设。一次相加只可能保持位数或增加一位。因此，若连续六个数全是素数，前五个数必有相同的奇数位数。
2. 任取其中连续三个素数 $x,y=T(x),T(y)$。用共同位权 $M$ 写 $x=M(10a+c)+b$，其中 $a,b$ 是两块，$c$ 是中间一位。令 $s=a+b$，则 $y=M(10s+2c)+s$。若 $s\ge M$，这个数已经至少为 $10M^2$，将增加位数，故 $s<M$。若 $2c<10$，$y$ 的左右两块都等于 $s$，旋转保持 $y$，从而 $T(y)=2y$ 为合数。于是中间一位必须进位，下一位是 $2c-10$。
3. 对六个假定的素数，以上进位关系可连用四次。若中间位依次为 $c_0,\ldots,c_4$，便有 $c_4+150=16c_0$。左边至少为 150，右边至多为 $16\times9=144$，矛盾。

## 在先结果与核验

2015 年，Chai Wah Wu 列出能保持四次的素数，并证明连续六次保持素性不可能。他给出的起点 10,010,905,789 在第四步得到 126,399,526,399。上述证明把此前公开的上界收紧到四次。源文件另外核对了该例每一步得到的整数。例子的五个数为素数这一事实出自 Wu 的记录。[四次实例和六次上界](https://oeis.org/A261458)

截至 2026 年 11 月 27 日，以四个 OEIS 编号、作者和猜想原文、交换两半的同义表述检索公开网页、论坛、论文及形式化记录，未发现五次上界的在先证明。Epoch 的 444 个 OEIS 序列元数据和 DeepMind 的 358 个 OEIS 目录项均未列入这几个编号。2023 年的一篇独立计算记录也把五次列作未知。检索范围无法确定全球优先权。[Epoch 元数据](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/metadata/oeis/sequences.json) · [DeepMind 目录](https://github.com/google-deepmind/formal-conjectures/tree/main/FormalConjectures/OEIS) · [2023 年的计算记录](https://voodooguru23.blogspot.com/2023/01/rotate-and-add.html)

本目录锁定 Lean 与 mathlib 4.24.0。在本目录运行

```sh
lake exe cache get Mathlib.Data.Nat.Log Mathlib.Data.Nat.Prime.Basic Mathlib.Tactic.Ring
lake env lean -DwarningAsError=true A086004.lean
```

[Lean 源码](A086004.lean)。定理名为 `RotateAdd.no_five_rotation_cycle_primes`。`#print axioms` 列出 `propext`、`Classical.choice`、`Quot.sound`。
