import NS.Families

/-!
# The growth rate

`D_3(n)` is the largest size of a square-difference-free set of polynomials of degree below `n`.
It is nondecreasing, at most `3^n`, and at least `810^e` at `n = 8e` by the first family. Writing
`L = log 810 / log 3`, the three facts give

`log D_3(n) / (n log 3) ≥ (1/8 - 1/n) · L` for `n ≥ 8`,

so the lower limit of the left side is at least `L/8`. Finally `16/21 ≤ L/8` is the natural-number
comparison `3^128 ≤ 810^21`, and `16/21 = 0.76190…` is the stated bound.
-/

namespace NS

open Polynomial

/-- The finite set `polyLT n` is exactly the set of polynomials of degree below `n`. -/
theorem mem_polyLT (n : ℕ) (f : (ZMod 3)[X]) : f ∈ polyLT n ↔ f.degree < n := by
  sorry

/-- There are at most `3^n` polynomials of degree below `n`. -/
theorem polyLT_card_le (n : ℕ) : (polyLT n).card ≤ 3 ^ n := by
  sorry

/-- The polynomials of degree below `n` sit inside those of degree below `n'` for `n ≤ n'`. -/
theorem polyLT_mono {n n' : ℕ} (h : n ≤ n') : polyLT n ⊆ polyLT n' := by
  sorry

/-- Every square-difference-free set of polynomials of degree below `n` is counted by `D_3(n)`. -/
theorem le_D3_of_sdf {n : ℕ} {A : Finset (ZMod 3)[X]} (hA : AllBelow n A) (hS : SDF A) :
    A.card ≤ D3 n := by
  sorry

/-- `D_3` is nondecreasing. -/
theorem D3_mono : Monotone D3 := by
  sorry

/-- `D_3(n) ≤ 3^n`, the trivial upper bound. -/
theorem D3_le (n : ℕ) : D3 n ≤ 3 ^ n := by
  sorry

/-- `D_3(n) ≥ 1`, witnessed by the one-element set `{0}`. -/
theorem one_le_D3 (n : ℕ) : 1 ≤ D3 n := by
  sorry

/-- The first family gives `D_3(8e) ≥ 810^e`. -/
theorem pow_le_D3 (e : ℕ) : 810 ^ e ≤ D3 (8 * e) := by
  sorry

/-- **The growth rate.** `16/21 = 0.76190… ≤ liminf log D_3(n) / (n log 3)`.

For `n ≥ 8` and `e = ⌊n/8⌋` the first family gives `D_3(n) ≥ D_3(8e) ≥ 810^e`, so the quotient is
at least `(1/8 - 1/n) log 810 / log 3`; letting `n` grow, the lower limit is at least
`log 810 / (8 log 3)`, and `16/21 ≤ log 810 / (8 log 3)` is the comparison `3^128 ≤ 810^21`. -/
theorem liminf_ge_internal :
    (16 / 21 : ℝ) ≤
      Filter.liminf (fun n : ℕ => Real.log (D3 n) / (n * Real.log 3)) Filter.atTop := by
  sorry

end NS
