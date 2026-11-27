"""Independent checks from starting sites, deterministic moves, and the Bell ket."""

import cmath
import math
from fractions import Fraction


def classical_counts(n):
    """For each Alice map, Bob chooses a best response at every starting site."""
    best = 0
    block = 0
    low = 0
    for mask in range(1 << n):
        destinations = [(x + (1 if mask & (1 << x) else -1)) % n for x in range(n)]
        loads = [0] * n
        for end in destinations:
            loads[end] += 1
        best = max(best, sum(max(loads[y - 1], loads[(y + 1) % n]) for y in range(n)))
        if all(end == (x + (1 if (x // 2) % 2 == 0 else -1)) % n
               for x, end in enumerate(destinations)):
            block = sum(load**2 for load in loads)
        if all(end == min((x - 1) % n, (x + 1) % n) for x, end in enumerate(destinations)):
            low = sum(load**2 for load in loads)
    return best, block, low


def tensor_win(n):
    """Contract the four amplitudes in the computational basis, then test meetings."""
    scale = 1 / math.sqrt(2)
    bell = ((scale, 0), (0, scale))
    k = (n + 2) // 4
    bases = []
    for x in range(n):
        phase = cmath.exp(2j * math.pi * k * x / n)
        bases.append({sign: (scale, sign * phase * scale) for sign in (-1, 1)})
    win = 0.0
    for x in range(n):
        for y in range(n):
            mass = 0.0
            for a in (-1, 1):
                for b in (-1, 1):
                    # Bob uses the conjugate of the basis used by Alice.
                    amp = sum(bases[x][a][s].conjugate() * bases[y][b][t] * bell[s][t]
                              for s in range(2) for t in range(2))
                    prob = abs(amp)**2
                    mass += prob
                    if (x + a) % n == (y + b) % n:
                        win += prob
            assert abs(mass - 1) < 1e-12
    return win / n**2


def defect(n):
    return (0, 1, 2, 1)[n % 4]


def main():
    alice_maps = 0
    pairs = 0
    for n in range(3, 16):
        best, block, low = classical_counts(n)
        assert best == block == 2 * n - defect(n)
        assert low == (5 if n == 3 else n + 4)
        alice_maps += 2**n
        pairs += 4**n
        if n < 10:
            print(f"C{n}: exact classical {Fraction(best, n*n)}, "
                  f"lowest-neighbour rule {Fraction(low, n*n)}")
    print(f"Classical N=3..15: {alice_maps:,} Alice maps; "
          f"{pairs:,} strategy pairs covered by exact best response.")
    for n in range(3, 42):
        quantum = (3 + math.cos(math.pi * defect(n) / n)) / (2 * n)
        assert abs(tensor_win(n) - quantum) < 1e-12
    print("Bell product-basis probabilities normalized on every input and "
          "direct meeting scores verified for N=3..41.")
    for n in range(3, 1025):
        multipliers = [abs(1 - cmath.exp(4j * math.pi * k / n))**2 for k in range(n)]
        spectral = 2 + 2 * math.cos(math.pi * defect(n) / n)
        assert abs(max(multipliers) - spectral) < 1e-12
        assert abs(multipliers[(n + 2) // 4] - spectral) < 1e-12
    print("All Fourier modes and the stated attaining mode checked for N=3..1024.")


if __name__ == "__main__":
    main()
