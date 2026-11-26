"""Exact tensor-Weyl tests of one-sided optimality; no external dependencies."""
from fractions import Fraction
from itertools import product

# Cyclotomic polynomials in increasing powers. Only the finite test uses this list.
CYCLOTOMIC = {2: (1,1), 3: (1,1,1), 4: (1,0,1), 5: (1,1,1,1,1), 6: (1,-1,1)}


def times(left, right):
    n = len(left)
    return [sum(left[i]*right[(k-i) % n] for i in range(n)) for k in range(n)]


def scalar(coefficients, cyclotomic):
    a = coefficients.copy()
    degree = len(cyclotomic)-1
    for k in range(len(a)-1, degree-1, -1):
        leading = a[k]
        for j, value in enumerate(cyclotomic):
            a[k-degree+j] -= leading*value
    assert all(x == 0 for x in a[1:])
    return a[0]


def direct_moments(state, orders):
    n = len(state)
    total = {m:[0]*n for m in orders}
    for a, b, h, d in product(range(n), repeat=4):
        correlation = [0]*n
        for i, j in product(range(n), repeat=2):
            correlation[(i*b+j*d) % n] += state[(i+a) % n][(j+h) % n]*state[i][j]
        squared = times(correlation, [correlation[-r % n] for r in range(n)])
        current = [1]+[0]*(n-1)
        for m in range(1,max(orders)+1):
            current = times(current, squared)
            if m in total:
                total[m] = [x+y for x,y in zip(total[m],current)]
    return tuple(scalar(total[m], CYCLOTOMIC[n]) for m in orders)


def matrix_product(left,right):
    n=len(left)
    return [[sum(left[i][k]*right[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def scaled_rotation(n,i,j):
    result=[[5*int(a==b) for b in range(n)] for a in range(n)]
    result[i][i]=result[j][j]=3
    result[i][j]=-4
    result[j][i]=4
    return result


def main():
    orders=(2,3,4)
    strict=0
    for n in CYCLOTOMIC:
        z=list(range(n,0,-1))
        second=(0,1) if n==2 else (1,2)
        U=matrix_product(scaled_rotation(n,0,1),scaled_rotation(n,*second))
        for a,b in product(range(n),repeat=2):
            assert sum(U[i][a]*U[i][b] for i in range(n))==625*int(a==b)
        moving=[[U[i][j]*z[j] for j in range(n)] for i in range(n)]
        aligned=[[25*z[j]*int(i==j) for j in range(n)] for i in range(n)]
        # A computational Weyl shift on A must preserve every moment exactly.
        shifted=[aligned[(i-1) % n] for i in range(n)]
        optimum=direct_moments(aligned,orders)
        assert direct_moments(shifted,orders)==optimum
        ratios=[Fraction(a,b) for a,b in zip(direct_moments(moving,orders),optimum)]
        assert all(q <= 1 for q in ratios)
        strict+=sum(q<1 for q in ratios)
        print(f'd={n}, moving/aligned moment ratios at orders {orders}: '+', '.join(f'{float(q):.6f}' for q in ratios))
    print(f'{strict} strict comparisons and {len(CYCLOTOMIC)*len(orders)} exact Weyl-shift equalities; comparisons used rational arithmetic.')


if __name__=='__main__':
    main()
