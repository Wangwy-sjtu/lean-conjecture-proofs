"""Exact Gaussian-integer cross-check of two-qubit signed Pauli spectra and their Clifford orbit."""
from collections import Counter, deque
from itertools import permutations, product

R = range(4)
ZERO, ONE, IM = (0, 0), (1, 0), (0, 1)

def add(a, b):
    return a[0]+b[0], a[1]+b[1]

def mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]

def scale(k, z):
    return k*z[0], k*z[1]

def conj(z):
    return z[0], -z[1]

def gsum(xs):
    total = ZERO
    for z in xs:
        total = add(total, z)
    return total

def matrix(fn, n=4):
    return tuple(tuple(fn(i,j) for j in range(n)) for i in range(n))

def mm(A, B):
    return matrix(lambda i,j: gsum(mul(A[i][k], B[k][j]) for k in R))

def kron(A, B):
    return matrix(lambda i,j: mul(A[i//2][j//2], B[i%2][j%2]))

def adj(A):
    return matrix(lambda i,j: conj(A[j][i]))

I = matrix(lambda i,j: (int(i == j),0), 2)
X = matrix(lambda i,j: (int(i != j),0), 2)
Y = ((ZERO,(0,-1)),(IM,ZERO))
Z = ((ONE,ZERO),(ZERO,(-1,0)))
PAULIS = [kron(a,b) for a,b in product((I,X,Y,Z), repeat=2)]
NONID = PAULIS[1:]
PERMS = [(p,(-1)**sum(p[i]>p[j] for i in R for j in range(i+1,4))) for p in permutations(R)]

def char_coeff(A):
    # det(tI - A) = t^4 - 30 t^2 + c*t + d by the trace form of Newton's identities.
    assert sum(A[i][i][0] for i in R) == 0
    assert sum(v[0]**2+v[1]**2 for row in A for v in row) == 60
    cube_trace = gsum(mul(mul(A[i][j], A[j][k]), A[k][i]) for i,j,k in product(R,repeat=3))
    assert not cube_trace[1] and cube_trace[0] % 3 == 0
    determinant = gsum(scale(s, mul(mul(A[0][p[0]], A[1][p[1]]),
                                     mul(A[2][p[2]], A[3][p[3]]))) for p,s in PERMS)
    assert determinant[1] == 0
    return -cube_trace[0]//3, determinant[0]

def exhaustive():
    summands = [[(i,j,p[i][j]) for i,j in product(R,repeat=2) if p[i][j] != ZERO] for p in NONID]
    A = [[gsum(p[i][j] for p in NONID) for j in R] for i in R]
    last = 0
    counts, winners = Counter(), set()
    for k in range(1<<15):
        mask = k ^ (k>>1)
        if k:
            flipped = mask ^ last
            delta = -2 if mask & flipped else 2
            for i,j,z in summands[flipped.bit_length()-1]:
                A[i][j] = add(A[i][j], scale(delta,z))
        coeff = char_coeff(A)
        counts[coeff] += 1
        if coeff == (-72,-27):
            winners.add(mask)
        last = mask
    return counts, winners

def clifford_orbit():
    H = ((ONE,ONE),(ONE,(-1,0)))
    S = ((ONE,ZERO),(ZERO,IM))
    cnot = matrix(lambda i,j: (int(i == (j ^ ((j>>1)&1))),0))
    gates = [(kron(H,I),2),(kron(I,H),2),(kron(S,I),1),(kron(I,S),1),(cnot,1)]
    lookup = {matrix(lambda i,j: scale(s,p[i][j])): (k,s) for k,p in enumerate(PAULIS) for s in (1,-1)}
    actions = []
    for u, divisor in gates:
        perm = []
        for p in NONID:
            conjp = mm(mm(adj(u),p),u)
            assert all(x % divisor == 0 for row in conjp for z in row for x in z)
            reduced = matrix(lambda i,j: tuple(x//divisor for x in conjp[i][j]))
            k, sign = lookup[reduced]
            perm.append((k-1, sign < 0))
        actions.append(perm)
    seen, queue = {0}, deque([0])
    while queue:
        mask = queue.popleft()
        for perm in actions:
            image = sum(((((mask>>j)&1)^flip)<<i) for i,(j,flip) in enumerate(perm))
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return seen

def main():
    counts, winners = exhaustive()
    expected = {(-72,-27):640,(-56,-27):1920,(-40,5):2304,(-24,69):3840,
                (-8,37):5760,(8,37):5760,(-8,165):1920,(24,69):3840,
                (40,5):2304,(8,165):1920,(56,-27):1920,(72,-27):640}
    assert counts == expected and sum(counts.values()) == 32768
    assert len(winners) == 640 and winners == clifford_orbit()
    print('32768 sign patterns. All 12 characteristic polynomial classes agree.')
    print('640 signs attain the largest root; they form the exact Clifford orbit of the all-positive sign vector.')

if __name__ == '__main__':
    main()
