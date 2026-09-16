import NS.Lift
import NS.Bases

/-!
# The two families

Iterating the lift from the two bases gives a square-difference-free subset of `P_{3,n}` for
every `n` divisible by `4`:

* `A_0 = {0}` and `A_{8e+8} = L_{8e}(A_{8e})`, of size `810^e` inside `P_{3,8e}`;
* `A_4 = B_4` and `A_{8e+12} = L_{8e+4}(A_{8e+4})`, of size `27 · 810^e` inside `P_{3,8e+4}`.

Each induction step needs the lift's three conclusions at an even degree bound: `8e` and `8e + 4`
are both even, which is why the two families together cover every multiple of `4`.
-/

namespace NS

open Polynomial

/-- The first family: `A_0 = {0}` and `A_{8e+8} = L_{8e}(A_{8e})`. -/
noncomputable def fam0 : ℕ → Finset (ZMod 3)[X]
  | 0 => base0
  | e + 1 => lift (8 * e) (fam0 e)

/-- The second family: `A_4 = B_4` and `A_{8e+12} = L_{8e+4}(A_{8e+4})`. -/
noncomputable def fam4 : ℕ → Finset (ZMod 3)[X]
  | 0 => base4
  | e + 1 => lift (8 * e + 4) (fam4 e)

/-- The `e`-th member of the first family lies in `P_{3,8e}`. -/
theorem fam0_allBelow (e : ℕ) : AllBelow (8 * e) (fam0 e) := by
  sorry

/-- The `e`-th member of the first family has `810^e` elements. -/
theorem fam0_card (e : ℕ) : (fam0 e).card = 810 ^ e := by
  sorry

/-- Every member of the first family is square-difference-free. -/
theorem fam0_sdf (e : ℕ) : SDF (fam0 e) := by
  sorry

/-- The `e`-th member of the second family lies in `P_{3,8e+4}`. -/
theorem fam4_allBelow (e : ℕ) : AllBelow (8 * e + 4) (fam4 e) := by
  sorry

/-- The `e`-th member of the second family has `27 · 810^e` elements. -/
theorem fam4_card (e : ℕ) : (fam4 e).card = 27 * 810 ^ e := by
  sorry

/-- Every member of the second family is square-difference-free. -/
theorem fam4_sdf (e : ℕ) : SDF (fam4 e) := by
  sorry

end NS
