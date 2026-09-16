# Square-difference-free sets in F_3[T] past the conjectured bound

Let `P_{q,n}` be the polynomials of degree less than `n` over the field with `q` elements, and call
a subset square-difference-free when no two of its elements differ by a nonzero square. Naslund
(*Paley graphs and Sárközy's theorem in function fields*, arXiv:2203.01293v3, Quart. J. Math. 74
(2023) 627–637) constructs, for `4 ∣ n`, a square-difference-free subset of `P_{q,n}` with
`q^{3n/4}` elements (Theorem 1), and conjectures that no square-difference-free subset of `P_{q,n}`
is larger (Conjecture 13, at `k = 2`). This repository proves that conjecture false at `q = 3`: the
bound `3^{3n/4}` fails for every `n ≡ 0 (mod 4)` with `n ≥ 8`.

The six theorems:

- a square-difference-free subset of `P_{3,8}` with 810 elements — `NS.D3_8_ge_810`;
- 810 exceeds the conjectured `3^6 = 729`, so the bound fails at `n = 8` — `NS.conjecture13_fails_3_2_8`;
- for every `e ≥ 1`, such a subset of `P_{3,8e}` with `810^e` elements — `NS.D3_8e_ge`;
- for every `e`, such a subset of `P_{3,8e+4}` with `27 · 810^e` elements — `NS.D3_8e4_ge`;
- the bound fails at every `n ≡ 0 (mod 4)` with `n ≥ 8` — `NS.conjecture13_fails_3_2_all`;
- `16/21 ≤ liminf log D_3(n) / (n log 3)`, where `D_3(n)` is the largest size of a
  square-difference-free subset of `P_{3,n}` — `NS.liminf_ge`.

One lift, applied repeatedly, gives all six. Fix the ten-word code
`S = {0000, 0211, 0121, 0112, 1200, 1020, 1002, 2212, 2122, 2221} ⊂ F_3^4`, in which no two words
differ by a vector with every coordinate in `{0, 1}`, the two squares of `F_3`. Put `P = T^3 - T`
and `Q = P^2`. For even `m` and a square-difference-free `B ⊆ P_{3,m}`, the polynomials
`V_s + P·R + Q·(b + s_∞ T^m + u T^{m+1})`, with `s ∈ S`, `R` of degree below 3, `u ∈ F_3` and
`b ∈ B`, form a square-difference-free subset of `P_{3,m+8}` with `810 · |B|` elements. Iterating
from the bases `{0} ⊆ P_{3,0}` and `B_4 = {aT^3 + bT + c(1 - T^2)} ⊆ P_{3,4}`, which has 27
elements, reaches every `n` divisible by 4.

`D_3(4) = 27`, so the conjectured bound holds with equality at `n = 4`; that value is stated as
data, and no upper bound is proved here, at `n = 4` or at any other `n`. No value of `D_3(n)` is
determined, the ten-word code is not claimed to be optimal, and nothing is claimed at any `q` other
than 3.

As of 2026-09-16 no published construction exceeds q^{3n/4} for square-difference-free subsets of
F_q[T]; Naslund's Conjecture 13 has two indexed citing papers, neither addressing it; the small
values I_3(3) = 4 and I_3(4) = 10 are stated as data whose prior appearance is under literature
review (Calderbank–Frankl–Graham–Li–Shepp 1993 give the LP bounds 5 and 11).

Run locally with the pinned Lean and Mathlib versions; there are no GitHub Actions workflows.

```sh
lake build
python scripts/check-source.py
python scripts/check_construction.py
```

[PROOF.md](PROOF.md) gives the mathematics with the Lean name of every step.
[VERIFICATION.md](VERIFICATION.md) records the checks and their limits, and
[DISCLOSURE.md](DISCLOSURE.md) the assistance statement. [Challenge.lean](Challenge.lean) states
the six theorems; [Solution.lean](Solution.lean) proves them.
