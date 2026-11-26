"""Compare the physical toggle matrix, row chasing, and binary polynomial gcd."""


def rank_binary(rows):
    pivots = {}
    for row in rows:
        while row:
            column = row.bit_length() - 1
            if column not in pivots:
                pivots[column] = row
                break
            row ^= pivots[column]
    return len(pivots)


def toggle_matrix(n):
    for row in range(n):
        for col in range(n):
            move = 0
            for i, j in ((row, col), (row - 1, col), (row + 1, col),
                         (row, col - 1), (row, col + 1)):
                if 0 <= i < n and 0 <= j < n:
                    move |= 1 << (n * i + j)
            yield move


def bottom_row(n, top):
    mask = (1 << n) - 1
    above, row = 0, top
    for _ in range(n):
        above, row = row, (above ^ row ^ (row << 1) ^ (row >> 1)) & mask
    return row


def path_poly(index, translate=False):
    older, current = 0, 1
    for _ in range(index):
        older, current = current, (current << 1) ^ (current if translate else 0) ^ older
    return older


def poly_gcd(a, b):
    while b:
        while a.bit_length() >= b.bit_length():
            a ^= b << (a.bit_length() - b.bit_length())
        a, b = b, a
    return a


def check_modes(n):
    # Columns and rows start at 1. These are the eigenmodes with eigenvalues
    # 0 and 1 of path adjacency, and their transposes.
    odd = sum(1 << (i - 1) for i in range(1, n + 1) if i % 2)
    not_third = sum(1 << (i - 1) for i in range(1, n + 1) if i % 3)
    assert {(row & 1, (row >> 1) & 1)
            for row in (0, odd, not_third, odd ^ not_third)} == {(0, 0), (0, 1), (1, 0), (1, 1)}
    for row in (0, odd, not_third, odd ^ not_third):
        assert bottom_row(n, row) == 0


if __name__ == "__main__":
    for n in range(1, 55):
        index = n + 1
        gcd = poly_gcd(path_poly(index), path_poly(index, True))
        nullity = n - rank_binary(bottom_row(n, 1 << i) for i in range(n))
        assert gcd.bit_length() - 1 == nullity
        if n <= 20 or n == 53:
            assert n * n - rank_binary(toggle_matrix(n)) == nullity
    print("Direct physical toggle matrices up to side 20 and at side 53 agree with row chasing; "
          "all sides from 1 through 54 also agree with the polynomial gcd.")
    for k in range(1, 10):
        index = 2 * 3**k
        assert poly_gcd(path_poly(index), path_poly(index, True)) == 0b110
        if k <= 6:
            check_modes(index - 1)
        if k <= 5:
            n = index - 1
            assert n - rank_binary(bottom_row(n, 1 << i) for i in range(n)) == 2
    print("The exact gcd is X^2+X for k=1..9 (largest side 39,365). "
          "All four explicit quiet top rows were checked through side 1,457.")

    from math import gcd as integer_gcd
    reduction_checks = 0
    for a in range(1, 48, 2):
        e = 1
        while pow(2, e, a) != (1 % a):
            e += 1
        for k in range(5):
            index = a**k
            if index > 4096:
                break
            small = integer_gcd(index, 2**e - 1)
            assert poly_gcd(path_poly(index), path_poly(index, True)) == poly_gcd(
                path_poly(small), path_poly(small, True))
            reduction_checks += 1
    for n, expected in [(56, 0), (170, 36), (512, 252)]:
        assert n - rank_binary(bottom_row(n, 1 << i) for i in range(n)) == expected
    for k, expected in [(1, 0), (2, 36), (3, 252)]:
        index = 57**k
        assert poly_gcd(path_poly(index), path_poly(index, True)).bit_length() - 1 == expected
    print(f"{reduction_checks} odd-power reductions passed. Direct unreduced polynomial counts "
          "on sides 56, 3,248, 185,192 agree with row chasing on sides 56, 170, 512.")


    # A primitive 3^(s+1)-st root is represented by X modulo
    # X^(2*3^s) + X^(3^s) + 1. All computations below are binary polynomial arithmetic.
    def residue_check(s):
        block = 3**s
        order = 3*block
        modulus = (1 << (2*block)) | (1 << block) | 1
        degree = 2*block

        def multiply(x, y):
            result = 0
            while y:
                if y & 1:
                    result ^= x
                y >>= 1
                x <<= 1
                if x >> degree:
                    x ^= modulus
            return result

        def power(x, n):
            result = 1
            while n:
                if n & 1:
                    result = multiply(result, x)
                x = multiply(x, x)
                n >>= 1
            return result

        def fib_at(t, n):
            left, right = 0, 1
            for digit in bin(n)[2:]:
                square = multiply(left, left)
                even = multiply(t, square)
                odd = square ^ multiply(right, right)
                if digit == '0':
                    left, right = even, odd
                else:
                    left, right = odd, multiply(t, odd) ^ even
            return left

        q = 4**block
        a = 3*((q-1)//order)*(q+1)
        assert power(2, order) == 1 and power(2, block) != 1
        t = 2 ^ power(2, order-1)
        assert fib_at(t, a**s) != 0
        assert fib_at(t, a**(s+1)) == fib_at(t ^ 1, a**(s+1)) == 0

    for s in range(1, 5):
        residue_check(s)
    print("Explicit finite-field witnesses certify a new common root at the selected "
          "transition s to s+1 for s=1,2,3,4.")

