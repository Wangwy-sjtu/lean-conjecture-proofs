"""Cross-check the physical seed supports and the finite-index calculations."""
from fractions import Fraction
from check_scaling import basis, chase, columns
from check_global import polynomial_nullities


def verify():
    assert [j for j, c in enumerate(columns(9, basis(9))) if c == 0] == [40]
    assert 0 not in columns(16, basis(16))
    for m in (9, 16):
        masks = basis(m)
        assert len(masks) == 8
        for b in masks:
            assert chase(m, b[0]) == (b, 0)
    indices = [10*5**k for k in range(5)] + [17**k for k in range(1, 4)]
    degrees = polynomial_nullities(max(indices))
    assert all(degrees[i-1] == 8 for i in indices)
    for i in (10, 17, 50, 250, 289):
        assert len(basis(i-1)) == 8
    first = 1 - Fraction(80, 2*100)
    second = 1 - Fraction(256, 2*289)
    assert (first, second) == (Fraction(3, 5), Fraction(161, 289))
    print(f"Verified physical support and dimensions; the two leading coefficients "
          f"are {first} and {second}. Checked {len(indices)} tower indices up to {max(indices)}.")


if __name__ == "__main__":
    verify()
