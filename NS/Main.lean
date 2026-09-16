import NS.Families
import NS.Asymptotics

/-!
# The six targets

Glue. The two families of `NS.Families` give the four existence statements once the internal
degree bound is converted to the public one, and the two refutations compare their sizes with the
conjectured bound `3^{3n/4}`: for `n = 8e` this is `3^{6e} = 729^e < 810^e`, and for `n = 8e + 4`
it is `3^{6e+3} = 27 · 729^e < 27 · 810^e`. The growth rate is the theorem of `NS.Asymptotics`.

The names of the pinned statement file are left free; `Solution.lean` declares them, with the
`_internal` theorems below as their proofs.
-/

namespace NS

open Polynomial

/-- **A square-difference-free subset of `P_{3,8}` with `810` elements**, the first lift of the
one-element base. -/
theorem D3_8_ge_810_internal :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT 8 A ∧ A.card = 810 ∧ SDF A := by
  sorry

/-- **The conjectured bound fails at `q = 3`, `k = 2`, `n = 8`:** not every square-difference-free
subset of `P_{3,8}` has at most `3^6 = 729` elements, since `810 > 729`. -/
theorem conjecture13_fails_3_2_8_internal :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)), DegLT 8 A → SDF A → A.card ≤ 3 ^ 6 := by
  sorry

/-- **The first family.** For every `e ≥ 1`, a square-difference-free subset of `P_{3,8e}` with
`810^e` elements. -/
theorem D3_8e_ge_internal (e : ℕ) (he : 1 ≤ e) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT (8 * e) A ∧ A.card = 810 ^ e ∧ SDF A := by
  sorry

/-- **The second family.** For every `e`, a square-difference-free subset of `P_{3,8e+4}` with
`27 · 810^e` elements. -/
theorem D3_8e4_ge_internal (e : ℕ) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegLT (8 * e + 4) A ∧ A.card = 27 * 810 ^ e ∧ SDF A := by
  sorry

/-- **The conjectured bound fails for every admissible `n ≥ 8`:** for `4 ∣ n` and `n ≥ 8`, not
every square-difference-free subset of `P_{3,n}` has at most `3^{3n/4}` elements. Such an `n` is
`8e` or `8e + 4` with `e ≥ 1`, and the corresponding family exceeds the bound by `(10/9)^e`. -/
theorem conjecture13_fails_3_2_all_internal (n : ℕ) (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)), DegLT n A → SDF A → A.card ≤ 3 ^ (3 * n / 4) := by
  sorry

end NS
