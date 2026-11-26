"""Exact Pauli checks on integer-amplitude states and all 480 fiducial vectors."""
from collections import deque
from fractions import Fraction
from math import log
from itertools import product

SIZE = range(4)
LABELS = list(product(SIZE, repeat=2))

def sign(z, j):
    return (-1) ** ((z & j).bit_count())

def overlaps(amps):
    norm = sum(round(z.real)**2 + round(z.imag)**2 for z in amps)
    result = []
    for x, z in LABELS:
        # i^(x.z) makes the Pauli string Hermitian, including the sign of YY.
        phase = 1j ** (x & z).bit_count()
        val = phase * sum(sign(z, j) * amps[x ^ j].conjugate() * amps[j] for j in SIZE)
        assert val.imag == 0 and val.real.is_integer()
        result.append(Fraction(int(val.real), norm))
    return tuple(result)

def pauli_matrix(x, z):
    coeff = 1j ** (x & z).bit_count()
    return tuple(tuple(coeff * sign(z, j) if i == x ^ j else 0 for j in SIZE) for i in SIZE)

def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))

def adj(a):
    return tuple(tuple(v.conjugate() for v in c) for c in zip(*a))

def kron(a, b):
    return tuple(tuple(a[i][j]*b[k][l] for j in range(len(a)) for l in range(len(b)))
                 for i in range(len(a)) for k in range(len(b)))

def conj_perms():
    id2, h, s = ((1,0),(0,1)), ((1,1),(1,-1)), ((1,0),(0,1j))
    cnot = tuple(tuple(int(i == (j ^ ((j >> 1) & 1))) for j in SIZE) for i in SIZE)
    paul = [pauli_matrix(x,z) for x,z in LABELS]
    data = {tuple(tuple(sgn*v for v in row) for row in mat): (i,sgn)
            for i,mat in enumerate(paul) for sgn in (1,-1)}
    gates = [(kron(h,id2),2),(kron(id2,h),2),(kron(s,id2),1),(kron(id2,s),1),(cnot,1)]
    for u, scale in gates:
        perm = []
        for mat in paul:
            conj = mul(mul(adj(u),mat),u)
            # Exact Gaussian integers divided by a power of two.
            key = tuple(tuple(v / scale for v in row) for row in conj)
            perm.append(data[key])
        yield perm

def main():
    fid = overlaps((1,1j,1j,1j))
    nonid = [q*q for q in fid[1:]]
    assert sum(nonid) == 3 and nonid.count(0) == 3 and nonid.count(Fraction(1,4)) == 12
    orbit, queue, generators = {fid}, deque([fid]), list(conj_perms())
    while queue:
        state = queue.popleft()
        for perm in generators:
            image = tuple(sgn*state[n] for n,sgn in perm)
            if image not in orbit:
                orbit.add(image)
                queue.append(image)
    assert len(orbit) == 480
    for state in orbit:
        assert state[0] == 1 and sum(q**4 for q in state[1:]) == Fraction(3,4)
    states = [(1,0,0,0), (1,1j,1j,1j), (1+2j,2-1j,-1j,3), (1,2,3j,4)]
    for state in states:
        qs = [r*r for r in overlaps(state)[1:]]
        assert sum(qs) == 3
        for alpha in (2,3,4):
            assert sum(q**alpha for q in qs) >= 3*Fraction(1,4)**(alpha-1)
        for alpha in (2.01,2.5,3.25,7.5):
            entropy = log((1+sum(float(q)**alpha for q in qs))/4)/(1-alpha)
            bound = log((1+3*0.25**(alpha-1))/4)/(1-alpha)
            assert entropy <= bound + 1e-12
    print("480 distinct exact Clifford-orbit Pauli vectors, each with 3 zeros and 12 absolute halves.")
    print("Four pure-state checks at three integer and four noninteger orders passed.")

if __name__ == "__main__":
    main()
