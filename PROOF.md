# The proof

The mathematics of the development, with the Lean name carrying each step. Everything lives in
the namespace `NS`; the modules are under `NS/`.

## Notation

Polynomials are `Polynomial (ZMod 3)`, and `ZMod 3` is the field with three elements. `P_{3,n}` is
the set of polynomials of degree less than `n`. A finite set `A` is *square-difference-free* when
`g - f = z^2` for `f, g ∈ A` forces `z = 0` (`NS.SDF`), and `A ⊆ P_{3,n}` is written
`∀ f ∈ A, f.natDegree < n` (`NS.DegLT`). `D_3(n)` is the largest size of a square-difference-free
set of polynomials of degree below `n` (`NS.D3`, over the finite set `NS.polyLT`).

The public bound `natDegree f < n` cannot express `P_{3,0} = {0}`, because the zero polynomial has
natural degree 0, and the recursion starts there. So the proofs use `degree f < n` in `WithBot ℕ`
(`NS.Below`, `NS.AllBelow`), where `n = 0` says `f = 0` (`NS.below_zero_iff`); the two agree for
`n ≥ 1` (`NS.below_iff_natDegree_lt`, `NS.allBelow_iff_degLT`).

The two squares of `F_3` are 0 and 1 (`NS.sq_eq_zero_or_one`), and `a^2 = 0` forces `a = 0`
(`NS.eq_zero_of_sq_eq_zero`).

## The code

`S = {0000, 0211, 0121, 0112, 1200, 1020, 1002, 2212, 2122, 2221} ⊆ F_3^4` (`NS.code`) has ten
words (`NS.code_card`). Its one property: two words whose difference has every coordinate in
`{0, 1}` are equal (`NS.code_property`). Both are finite checks over `Fin 4 → ZMod 3`, decided by
the kernel.

## The lift

Write `P = T^3 - T` (`NS.P`) and `Q = P^2 = T^6 + T^4 + T^2` (`NS.Q`, `NS.Q_eq`). `P` vanishes at
every element of `F_3` (`NS.eval_P`), hence so does `Q` (`NS.eval_Q`); `P` has degree 3
(`NS.degree_P`) and `Q` degree 6 (`NS.degree_Q`), with `[T^5] Q = 0` (`NS.coeff_Q_five`) and
`[T^6] Q = 1` (`NS.coeff_Q_six`). For `s ∈ F_3^4`,
`V_s = s_0 + (s_2 - s_1) T - (s_0 + s_1 + s_2) T^2` (`NS.V`) has degree at most 2
(`NS.degree_V_le`) and takes the value `s_c` at `c = 0, 1, 2` (`NS.eval_V_zero`, `NS.eval_V_one`,
`NS.eval_V_two`). `R_r` is the general polynomial of degree below 3 (`NS.R`), determined by its
coefficients (`NS.R_injective`).

Let `m` be even and `B ⊆ P_{3,m}` square-difference-free. The lift is

`L_m(B) = { V_s + P·R_r + Q·(b + s_∞ T^m + u T^{m+1}) : s ∈ S, r ∈ F_3^3, u ∈ F_3, b ∈ B }`

(`NS.liftMap` on the parameter set `NS.params`; `NS.tail` is the factor `Q` multiplies, and the
lifted set is `NS.lift`). It has four properties.

*Degree.* `V_s + P·R_r` has degree at most 5 (`NS.degree_V_add_P_mul_R_le`) and the tail degree
below `m + 2`, so multiplying by `Q` stays below `m + 8` (`NS.Below.Q_mul`); hence
`L_m(B) ⊆ P_{3,m+8}` (`NS.liftMap_below`, `NS.lift_allBelow`).

*Signature.* Since `P` and `Q` vanish on `F_3`, a lifted polynomial takes the value `s_c` at `c`
(`NS.eval_liftMap_zero`, `NS.eval_liftMap_one`, `NS.eval_liftMap_two`). Its coefficient at
`T^{m+6}` is `s_∞` (`NS.coeff_liftMap_top`): `V_s + P·R_r` has degree at most `5 < m + 6`; every
term of `Q·b` has index `m + 6 - j > 6` for some `j < m`, so contributes nothing; `Q · s_∞ T^m`
contributes `s_∞` times the leading coefficient of `Q`; and `Q · u T^{m+1}` would need `[T^5] Q`,
which vanishes.

*Injectivity.* If two tuples lift to the same polynomial, then
`(V_s + P·R_r) - (V_{s'} + P·R_{r'}) = Q · (tail' - tail)`, whose left side has degree below 6, so
both sides vanish (`NS.eq_zero_of_Q_dvd_of_degree_lt`). Evaluating at 0, 1 and 2 gives
`s_0, s_1, s_2`; the top coefficient gives `s_∞`; cancelling `P` gives `r = r'`; and the
coefficients of the tail at `T^m` and `T^{m+1}` give `b` and `u`. No division algorithm is needed
(`NS.liftMap_injOn`). The parameter set has `10 · 27 · 3 · |B|` elements (`NS.params_card`), so
`|L_m(B)| = 810 · |B|` (`NS.lift_card`).

*No square differences.* Suppose `g - f = z^2` with `f, g ∈ L_m(B)` coming from `(s, r, u, b)` and
`(s', r', u', b')`. Then `deg z^2 ≤ m + 7`, and `m` is even, so `deg z ≤ m/2 + 3` and
`[T^{m+6}] z^2 = ([T^{m/2+3}] z)^2`. Together with the values at 0, 1, 2, this makes all four
coordinates of `s' - s` squares in `F_3`, hence in `{0, 1}`, so `s = s'` by the code property.
Then `z` vanishes on `F_3`, so `P ∣ z` (`NS.P_dvd_of_eval`, which rests on
`NS.eq_zero_of_degree_le_two_of_eval`); writing `z = P·w` gives `z^2 = Q·w^2`. The `V` terms
cancel, `Q` divides `g - f`, and `P·(R_{r'} - R_r)` has degree below 6, so it vanishes; cancelling
`Q` leaves `(b' - b) + (u' - u) T^{m+1} = w^2`. A nonzero square has even degree while `m + 1` is
odd, so `u = u'`, and then `b' - b = w^2` forces `w = 0` because `B` is square-difference-free
(`NS.lift_sdf`).

## The bases

`B_0 = {0} ⊆ P_{3,0}` is square-difference-free and has one element (`NS.base0`, `NS.base0_card`,
`NS.base0_allBelow`, `NS.base0_sdf`).

`B_4 = { a T^3 + b T + c (1 - T^2) : a, b, c ∈ F_3 } ⊆ P_{3,4}` (`NS.base4`, built from
`NS.base4Map`) has 27 elements, because the coefficients at `T^3`, `T` and 1 read `a`, `b` and `c`
back (`NS.base4Map_injective`, `NS.base4_card`, `NS.base4_allBelow`). It is square-difference-free
(`NS.base4_sdf`): a difference of two elements has constant term `c` and `T^2`-coefficient `-c`,
while a nonzero square of degree below 4 is `(v + uT)^2`, with constant term `v^2` and
`T^2`-coefficient `u^2`; so `v^2 + u^2 = 0`, and in `F_3` that forces `u = v = 0`
(`NS.eq_zero_of_sq_add_sq`).

## The families

Iterating the lift from the two bases gives `A_0 = {0}`, `A_{8e+8} = L_{8e}(A_{8e})` (`NS.fam0`)
and `A_4 = B_4`, `A_{8e+12} = L_{8e+4}(A_{8e+4})` (`NS.fam4`). The bounds `8e` and `8e + 4` are
even, which is what the lift asks of `m`, so induction gives the degree bound, the size and
square-difference-freeness of each member (`NS.fam0_allBelow`, `NS.fam0_card`, `NS.fam0_sdf`,
`NS.fam4_allBelow`, `NS.fam4_card`, `NS.fam4_sdf`).

The first member of the first family is a square-difference-free subset of `P_{3,8}` with 810
elements (`NS.D3_8_ge_810_internal`), and `810 > 729 = 3^6` (`NS.conjecture13_fails_3_2_8_internal`).
In general the families give `810^e` inside `P_{3,8e}` and `27 · 810^e` inside `P_{3,8e+4}`
(`NS.D3_8e_ge_internal`, `NS.D3_8e4_ge_internal`), against the conjectured `3^{6e} = 729^e` and
`3^{6e+3} = 27 · 729^e`. Both ratios are `(10/9)^e`, which exceeds 1 for `e ≥ 1`. Every
`n ≡ 0 (mod 4)` with `n ≥ 8` is `8e` or `8e + 4` with `e ≥ 1`, so the conjectured bound fails at
all of them (`NS.conjecture13_fails_3_2_all_internal`).

## The liminf

`polyLT n` is exactly the set of polynomials of degree below `n` (`NS.mem_polyLT`), of size at
most `3^n` (`NS.polyLT_card_le`) and increasing in `n` (`NS.polyLT_mono`). So `D_3` counts every
square-difference-free set of the right degree (`NS.le_D3_of_sdf`), is nondecreasing
(`NS.D3_mono`), is at least 1 (`NS.one_le_D3`) and at most `3^n` (`NS.D3_le`), and the first
family gives `D_3(8e) ≥ 810^e` (`NS.pow_le_D3`).

For `n ≥ 8` and `e = ⌊n/8⌋`, monotonicity gives
`log D_3(n) / (n log 3) ≥ (1/8 - 1/n) · log 810 / log 3`, so the lower limit is at least
`log 810 / (8 log 3)`. That the limit exceeds `16/21` is the comparison of natural numbers
`3^128 ≤ 810^21`; since `810 = 81 · 10`, this is `10^21 > 3^44`, and
`10^21 = 1000000000000000000000` while `3^44 = 984770902183611232881`. The conclusion is
`16/21 ≤ liminf log D_3(n) / (n log 3)` (`NS.liminf_ge_internal`), and `16/21 = 0.76190…` exceeds
`0.7619` by `1/210000`.

## References

- Eric Naslund, *Paley graphs and Sárközy's theorem in function fields*, Quart. J. Math. 74
  (2023), no. 2, 627–637, arXiv:2203.01293v3, doi:10.1093/qmath/haac035. Theorem 1 is the
  `q^{3n/4}` construction for odd `q`; Conjecture 13, at `k = 2`, is the statement refuted here.
- Imre Z. Ruzsa, *Difference sets without squares*, Period. Math. Hungar. 15 (1984), no. 3,
  205–209, doi:10.1007/BF02454169. The digit construction that Naslund's Theorem 1 adapts.
- A. R. Calderbank, P. Frankl, R. L. Graham, W.-C. W. Li and L. A. Shepp, *The Sperner capacity of
  linear and nonlinear codes for the cyclic triangle*, J. Algebraic Combin. 2 (1993), no. 1,
  31–48, doi:10.1023/A:1022424630332. The setting of the ten-word code: a linear code has at most
  `3^{n/2}` words, so 9 at `n = 4`, and the LP bound there is 11.
- Aart Blokhuis, *On the Sperner capacity of the cyclic triangle*, J. Algebraic Combin. 2 (1993),
  no. 2, 123–124, doi:10.1023/A:1022455407000. The upper bound `2^n` in the same setting.
