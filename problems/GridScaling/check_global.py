"""Independent small-dimensional audit of the common-modulus reduction."""
from functools import lru_cache
from math import gcd, lcm, prod
from check_scaling import basis, columns


def remainder(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def times_x(v, p, shifted):
    return remainder((v << 1) ^ (v if shifted else 0), p)


def first_rank(p, shifted):
    if p <= 1:
        return 1
    prev, cur = 0, 1
    for n in range(1, 1 << (2 * (p.bit_length() - 1))):
        if cur == 0:
            return n
        prev, cur = cur, times_x(cur, p, shifted) ^ prev
    if cur == 0:
        return n + 1
    raise AssertionError(f"finite invertible recurrence did not return for polynomial {p}")


def joint_rank(p):
    return lcm(first_rank(p, False), first_rank(p, True))


def polynomial_nullities(limit):
    values = []
    a, b = 0, 1
    c, d = 0, 1
    for _ in range(limit):
        a, b = b, (b << 1) ^ a
        c, d = d, (d << 1) ^ d ^ c
        u, v = a, c
        while v:
            u, v = v, remainder(u, v)
        values.append(u.bit_length() - 1)
    return values


@lru_cache(maxsize=None)
def physical(n):
    b = basis(n)
    return len(b), sum(t != 0 for t in columns(n, b))


def known(n, nullity):
    if nullity == 0:
        return n * n
    if nullity == 2:
        q, rem = divmod(n + 1, 6)
        assert rem == 0
        return 26*q*q - 12*q + 1
    if nullity == 4:
        q, rem = divmod(n + 1, 5)
        assert rem == 0 and q % 2 == 1
        return 17*q*q - 10*q
    if nullity == 6:
        q, rem = divmod(n + 1, 12)
        assert rem == 0 and q % 2 == 1
        return 88*q*q - 24*q + 1
    raise ValueError(nullity)


def check():
    cap = 720
    degrees = polynomial_nullities(cap)
    tested = smaller = costs = 0
    for bound in range(7):
        L = prod(joint_rank(p) for p in range(1 << (bound + 1)))
        for n, actual in enumerate(degrees):
            if actual > bound:
                continue
            N = n + 1
            a = gcd(N, L)
            assert degrees[a - 1] == actual
            assert gcd(N % (2*L), L) == a and N//a % 2 == (N % (2*L))//a % 2
            tested += 1
            smaller += a < N
            if n >= 200:
                continue
            sd, H = physical(a - 1)
            assert sd == physical(n)[0] == actual
            Q = N//a
            deficit = 2*(a-1)**2 - H - 2*known(a-1, actual)
            assert 2*known(n, actual) + Q*Q*H + (Q % 2)*deficit == 2*n*n
            costs += 1
    print(f"{tested} bounded-nullity index reductions, including {smaller} strictly "
          f"smaller seeds. Verified {costs} exact press formulas independently "
          f"with physical row chasing on sides below 200.")


if __name__ == '__main__':
    check()
