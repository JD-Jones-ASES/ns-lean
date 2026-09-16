#!/usr/bin/env python3
"""Rebuild the construction outside Lean and check its finite facts.

The script uses the standard library only and exact integer arithmetic. It rebuilds the ten-word
code, the polynomials of the lift, the two bases and the lifted sets, and checks the code
property, the interpolant identities, the sizes and degree bounds, the absence of square
differences, and the numerical comparisons. Two controls that must fail are run at the end.

This is a cross-check, not a proof. Nothing here is a premise of any Lean theorem, and the Lean
development does not read this file.
"""

import itertools
import sys

HALF = 3 ** 6


def fail(message):
    print("FAILED: " + message)
    sys.exit(1)


# --- polynomials over F_3, little-endian coefficient tuples with no trailing zeros -------------

def trim(coeffs):
    size = len(coeffs)
    while size > 0 and coeffs[size - 1] == 0:
        size -= 1
    return tuple(coeffs[:size])


def add(a, b):
    width = max(len(a), len(b))
    out = []
    for i in range(width):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        out.append((x + y) % 3)
    return trim(out)


def mul(a, b):
    if not a or not b:
        return ()
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % 3
    return trim(out)


def value(a, point):
    total = 0
    for x in reversed(a):
        total = (total * point + x) % 3
    return total


def coeff(a, index):
    return a[index] if index < len(a) else 0


def monomial(c, index):
    if c % 3 == 0:
        return ()
    return tuple([0] * index + [c % 3])


def degree_below(a, n):
    return len(a) <= n


def polys_below(n):
    return [trim(c) for c in itertools.product(range(3), repeat=n)]


def key(a):
    total = 0
    place = 1
    for x in a:
        total += x * place
        place *= 3
    return total


# --- the construction --------------------------------------------------------------------------

CODE = ((0, 0, 0, 0), (0, 2, 1, 1), (0, 1, 2, 1), (0, 1, 1, 2), (1, 2, 0, 0), (1, 0, 2, 0),
        (1, 0, 0, 2), (2, 2, 1, 2), (2, 1, 2, 2), (2, 2, 2, 1))

P = (0, 2, 0, 1)
Q = mul(P, P)


def interpolant(s):
    return trim([s[0] % 3, (s[2] - s[1]) % 3, (-(s[0] + s[1] + s[2])) % 3])


def lift(m, base):
    out = []
    for s in CODE:
        head_s = interpolant(s)
        for r in itertools.product(range(3), repeat=3):
            head = add(head_s, mul(P, trim(list(r))))
            for u in range(3):
                extra = add(monomial(s[3], m), monomial(u, m + 1))
                for b in base:
                    out.append(add(head, mul(Q, add(b, extra))))
    return out


def base4():
    out = []
    for a, b, c in itertools.product(range(3), repeat=3):
        out.append(add(add(monomial(a, 3), monomial(b, 1)),
                       mul(monomial(c, 0), (1, 0, 2))))
    return out


def code_property(words):
    for s in words:
        for t in words:
            if s != t:
                if all((t[i] - s[i]) % 3 in (0, 1) for i in range(4)):
                    return False
    return True


def nonzero_squares_below(n):
    out = set()
    for z in polys_below((n + 1) // 2):
        if z:
            out.add(mul(z, z))
    return out


def build_add(digits):
    if digits == 1:
        return [[(a + b) % 3 for b in range(3)] for a in range(3)]
    split = digits // 2
    low = build_add(split)
    high = build_add(digits - split)
    base = 3 ** split
    top = 3 ** (digits - split)
    table = []
    for a in range(base * top):
        a_high, a_low = divmod(a, base)
        row_low = low[a_low]
        row_high = high[a_high]
        row = [0] * (base * top)
        for b_high in range(top):
            shift = row_high[b_high] * base
            offset = b_high * base
            for b_low in range(base):
                row[offset + b_low] = row_low[b_low] + shift
        table.append(row)
    return table


ADD = build_add(6)


def has_square_difference(elements, squares):
    """True when two elements differ by one of the given nonzero squares."""
    present = set(key(f) for f in elements)
    parts = [divmod(k, HALF) for k in present]
    for square in squares:
        high, low = divmod(key(square), HALF)
        table_low = ADD[low]
        table_high = ADD[high]
        shifted = set(table_low[p[1]] + HALF * table_high[p[0]] for p in parts)
        if not present.isdisjoint(shifted):
            return True
    return False


# --- the checks ----------------------------------------------------------------------------------

def main():
    report = []

    words = set(CODE)
    if len(words) != 10:
        fail("the code does not have ten distinct words")
    if not code_property(CODE):
        fail("two words of the code differ by a vector with every coordinate in {0, 1}")
    report.append("code: 10 distinct words, and no two of the 90 ordered pairs of distinct words "
                  "differ by a vector with every coordinate in {0, 1}")

    for c in range(3):
        if value(P, c) != 0 or value(Q, c) != 0:
            fail("P or Q does not vanish on F_3")
    if Q != (0, 0, 1, 0, 1, 0, 1) or coeff(Q, 5) != 0 or coeff(Q, 6) != 1:
        fail("Q is not T^6 + T^4 + T^2")
    report.append("polynomials: P = T^3 - T and Q = P^2 vanish on F_3, "
                  "Q = T^6 + T^4 + T^2, [T^5] Q = 0 and [T^6] Q = 1")

    identities = 0
    for s in itertools.product(range(3), repeat=4):
        for c in range(3):
            if value(interpolant(s), c) != s[c]:
                fail("V_s(c) is not s_c")
            identities += 1
    report.append("interpolants: V_s(c) = s_c for all 81 words s and c = 0, 1, 2 "
                  "({0} identities)".format(identities))

    a8 = lift(0, [()])
    if len(set(a8)) != 810:
        fail("L_0({0}) does not have 810 distinct elements")
    for f in a8:
        if not degree_below(f, 8):
            fail("an element of L_0({0}) has degree 8 or more")
    report.append("L_0({0}): 810 distinct polynomials, every one of degree below 8")

    preimage = set()
    for f in polys_below(8):
        if (value(f, 0), value(f, 1), value(f, 2), coeff(f, 6)) in words:
            preimage.add(f)
    if preimage != set(a8):
        fail("L_0({0}) is not the preimage of the code")
    report.append("L_0({0}): equals the 810 polynomials f of degree below 8 whose signature "
                  "(f(0), f(1), f(2), [T^6] f) lies in the code")

    squares8 = nonzero_squares_below(8)
    if len(squares8) != 40:
        fail("there are not 40 nonzero squares of degree below 8")
    if has_square_difference(set(a8), squares8):
        fail("two elements of L_0({0}) differ by a nonzero square")
    report.append("L_0({0}): no two elements differ by one of the 40 nonzero squares of degree "
                  "below 8 (32400 tests)")

    b4 = base4()
    if len(set(b4)) != 27:
        fail("B_4 does not have 27 distinct elements")
    for f in b4:
        if not degree_below(f, 4):
            fail("an element of B_4 has degree 4 or more")
    report.append("B_4: 27 distinct polynomials, every one of degree below 4")

    squares4 = nonzero_squares_below(4)
    if len(squares4) != 4:
        fail("there are not 4 nonzero squares of degree below 4")
    if has_square_difference(set(b4), squares4):
        fail("two elements of B_4 differ by a nonzero square")
    report.append("B_4: no two elements differ by one of the 4 nonzero squares of degree below 4 "
                  "(108 tests)")

    l4 = lift(4, b4)
    if len(set(l4)) != 21870:
        fail("L_4(B_4) does not have 21870 distinct elements")
    for f in l4:
        if not degree_below(f, 12):
            fail("an element of L_4(B_4) has degree 12 or more")
    report.append("L_4(B_4): 21870 distinct polynomials, every one of degree below 12")

    squares12 = nonzero_squares_below(12)
    if len(squares12) != 364:
        fail("there are not 364 nonzero squares of degree below 12")
    if has_square_difference(set(l4), squares12):
        fail("two elements of L_4(B_4) differ by a nonzero square")
    report.append("L_4(B_4): no two elements differ by one of the 364 nonzero squares of degree "
                  "below 12 (7960680 tests)")

    if not (810 > 3 ** 6 and 27 * 810 > 3 ** 9):
        fail("the sizes do not exceed the conjectured bound")
    report.append("sizes: 810 > 729 = 3^6 and 21870 > 19683 = 3^9")

    if not 10 ** 21 > 3 ** 44:
        fail("10^21 > 3^44 is false")
    report.append("growth: 10^21 = 1000000000000000000000 > 984770902183611232881 = 3^44")

    if not 16 * 10000 > 21 * 7619:
        fail("16/21 > 7619/10000 is false")
    report.append("decimal: 16/21 > 7619/10000, since 160000 > 159999")

    broken = list(CODE[:-1]) + [(1, 1, 1, 1)]
    if code_property(broken):
        fail("the control code with the word 2221 replaced by 1111 passed the code property")
    report.append("control: the code with 2221 replaced by 1111 fails the code property, as it "
                  "must")

    if not has_square_difference({(), (1,)}, nonzero_squares_below(2)):
        fail("the control base {0, 1} passed the square-difference test")
    report.append("control: the set {0, 1} of polynomials of degree below 2 has the square "
                  "difference 1 = 1^2, as it must")

    for line in report:
        print(line)
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
