import NS.Main

/-!
# Square-difference-free sets in `F_3[T]`: Naslund's Conjecture 13 fails at `q = 3`

The six statements of `Challenge.lean`, restated verbatim and discharged from `NS.Main`.
The definitions they mention — `SDF`, `DegLT`, `polyLT`, `D3` — are the ones of `NS.Defs`,
again verbatim. This file does not import `Challenge.lean`.
-/

namespace NS

/-- **A square-difference-free subset of `P_{3,8}` with `810` elements.** -/
theorem D3_8_ge_810 :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT 8 A ∧ A.card = 810 ∧ SDF A := by
  exact D3_8_ge_810_internal

/-- **Conjecture 13 fails at `q = 3`, `k = 2`, `n = 8`:** not every square-difference-free subset
of `P_{3,8}` has at most `3^6 = 729` elements. -/
theorem conjecture13_fails_3_2_8 :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)), DegLT 8 A → SDF A → A.card ≤ 3 ^ 6 := by
  exact conjecture13_fails_3_2_8_internal

/-- **The first family.** For every `e ≥ 1`, a square-difference-free subset of `P_{3,8e}` with
`810^e` elements. -/
theorem D3_8e_ge (e : ℕ) (he : 1 ≤ e) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT (8 * e) A ∧ A.card = 810 ^ e ∧ SDF A := by
  exact D3_8e_ge_internal e he

/-- **The second family.** For every `e`, a square-difference-free subset of `P_{3,8e+4}` with
`27 · 810^e` elements. -/
theorem D3_8e4_ge (e : ℕ) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT (8 * e + 4) A ∧ A.card = 27 * 810 ^ e ∧ SDF A := by
  exact D3_8e4_ge_internal e

/-- **Conjecture 13 fails at `q = 3`, `k = 2`, for every admissible `n ≥ 8`:** for `4 ∣ n` and
`n ≥ 8`, not every square-difference-free subset of `P_{3,n}` has at most `3^{3n/4}` elements. -/
theorem conjecture13_fails_3_2_all (n : ℕ) (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)), DegLT n A → SDF A → A.card ≤ 3 ^ (3 * n / 4) := by
  exact conjecture13_fails_3_2_all_internal n h4 h8

/-- **The growth rate.** `16/21 = 0.7619… ≤ liminf log D_3(n) / (n log 3)`. -/
theorem liminf_ge :
    (16 / 21 : ℝ) ≤
      Filter.liminf (fun n : ℕ => Real.log (D3 n) / (n * Real.log 3)) Filter.atTop := by
  exact liminf_ge_internal

end NS
