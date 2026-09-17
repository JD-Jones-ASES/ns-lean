import Mathlib

/-!
# Square-difference-free sets in `F_3[T]`: Naslund's Conjecture 13 fails at `q = 3`

Let `P_{3,n}` be the polynomials of degree less than `n` over the field with three elements, and
call a set `A ⊆ P_{3,n}` *square-difference-free* when no two of its elements differ by a nonzero
square. Write `D_3(n)` for the largest size of such a set. For odd `q` and `4 ∣ n`, Naslund
(*Paley graphs and Sárközy's theorem in function fields*, arXiv:2203.01293v3, Theorem 1)
constructs a square-difference-free subset of `P_{q,n}` with `q^{3n/4}` elements, and conjectures
(Conjecture 13, at `k = 2`) that no square-difference-free subset of `P_{q,n}` is larger: for
`q = 3` this says `D_3(n) ≤ 3^{3n/4}` whenever `4 ∣ n`.

This file states that the conjectured inequality fails at `q = 3` for every `n ≡ 0 (mod 4)` with
`n ≥ 8`, and that the growth rate of `D_3(n)` is at least `16/21` in base `3`.

## What is claimed

* `D3_8_ge_810`: a square-difference-free subset of `P_{3,8}` with `810` elements.
* `conjecture13_fails_3_2_8`: since `810 > 729 = 3^6`, the conjectured bound fails at `n = 8`.
* `D3_8e_ge`, `D3_8e4_ge`: for every `e ≥ 1` a square-difference-free subset of `P_{3,8e}` with
  `810^e` elements, and for every `e ≥ 0` one of `P_{3,8e+4}` with `27 · 810^e` elements.
* `conjecture13_fails_3_2_all`: the conjectured bound `3^{3n/4}` fails for every `n ≡ 0 (mod 4)`
  with `n ≥ 8`.
* `liminf_ge`: `16/21 ≤ liminf log D_3(n) / (n log 3)`.

## Conventions

Polynomials are `Polynomial (ZMod 3)`; `ZMod 3` is the field with three elements. "Degree below
`n`" is `natDegree f < n`; for `n ≥ 1` this is exactly membership in `P_{3,n}` (the zero
polynomial has `natDegree 0`). Sets are `Finset (Polynomial (ZMod 3))`. A set is
square-difference-free when `g - f = z ^ 2` for two of its elements forces `z = 0`. `D3 n` is the
largest cardinality of a square-difference-free subset of the finite set of polynomials of degree
below `n`. Logarithms are natural logarithms, and `3 * n / 4` is natural-number division (exact
whenever `4 ∣ n`).

This Mathlib-only file intentionally contains `sorry` placeholders. The corresponding
declarations are proved in `Solution.lean`, which does not import this file.
-/

namespace NS

/-- A finite set of polynomials over `F_3` is *square-difference-free*: no two of its elements
differ by a nonzero square. -/
def SDF (A : Finset (Polynomial (ZMod 3))) : Prop :=
  ∀ f ∈ A, ∀ g ∈ A, ∀ z : Polynomial (ZMod 3), g - f = z ^ 2 → z = 0

/-- Every element of `A` has degree below `n`. For `n ≥ 1` this says `A ⊆ P_{3,n}`, the
polynomials of degree less than `n` (the zero polynomial has `natDegree 0`). -/
def DegLT (n : ℕ) (A : Finset (Polynomial (ZMod 3))) : Prop :=
  ∀ f ∈ A, f.natDegree < n

/-- The polynomials of degree below `n` over `F_3`, as a finite set: the image of the coefficient
vectors `Fin n → ZMod 3` under `c ↦ Σ c_i T^i`. -/
noncomputable def polyLT (n : ℕ) : Finset (Polynomial (ZMod 3)) :=
  open scoped Classical in
  (Finset.univ : Finset (Fin n → ZMod 3)).image
    (fun c => ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))

/-- `D3 n`: the largest size of a square-difference-free set of polynomials of degree below `n`
over `F_3`. -/
noncomputable def D3 (n : ℕ) : ℕ :=
  open scoped Classical in
  ((polyLT n).powerset.filter SDF).sup Finset.card

/-- **A square-difference-free subset of `P_{3,8}` with `810` elements.** -/
theorem D3_8_ge_810 :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT 8 A ∧ A.card = 810 ∧ SDF A := by
  sorry

/-- **Conjecture 13 fails at `q = 3`, `k = 2`, `n = 8`:** not every square-difference-free subset
of `P_{3,8}` has at most `3^6 = 729` elements. -/
theorem conjecture13_fails_3_2_8 :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)), DegLT 8 A → SDF A → A.card ≤ 3 ^ 6 := by
  sorry

/-- **The first family.** For every `e ≥ 1`, a square-difference-free subset of `P_{3,8e}` with
`810^e` elements. -/
theorem D3_8e_ge (e : ℕ) (he : 1 ≤ e) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT (8 * e) A ∧ A.card = 810 ^ e ∧ SDF A := by
  sorry

/-- **The second family.** For every `e`, a square-difference-free subset of `P_{3,8e+4}` with
`27 · 810^e` elements. -/
theorem D3_8e4_ge (e : ℕ) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT (8 * e + 4) A ∧ A.card = 27 * 810 ^ e ∧ SDF A := by
  sorry

/-- **Conjecture 13 fails at `q = 3`, `k = 2`, for every admissible `n ≥ 8`:** for `4 ∣ n` and
`n ≥ 8`, not every square-difference-free subset of `P_{3,n}` has at most `3^{3n/4}` elements. -/
theorem conjecture13_fails_3_2_all (n : ℕ) (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)), DegLT n A → SDF A → A.card ≤ 3 ^ (3 * n / 4) := by
  sorry

/-- **The growth rate.** `16/21 = 0.76190… ≤ liminf log D_3(n) / (n log 3)`. -/
theorem liminf_ge :
    (16 / 21 : ℝ) ≤
      Filter.liminf (fun n : ℕ => Real.log (D3 n) / (n * Real.log 3)) Filter.atTop := by
  sorry

end NS
