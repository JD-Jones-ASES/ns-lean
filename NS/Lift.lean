import NS.Code
import NS.Poly
import NS.Below

/-!
# The lift

Given an even `m` and a square-difference-free set `B` of polynomials of degree below `m`, the
lift is

`L_m(B) = { V_s + P·R_r + Q·(b + s_∞ T^m + u T^{m+1}) : s ∈ S, r ∈ F_3^3, u ∈ F_3, b ∈ B }`,

a set of polynomials of degree below `m + 8` with exactly `810 · |B|` elements, again
square-difference-free.

Three features of the formula do the work. The values of a lifted polynomial at `0, 1, 2` are
`s_0, s_1, s_2`, because `P` and `Q` vanish there; its coefficient at `T^{m+6}` is `s_∞`, because
`Q` has degree `6` and no `T^5` term; and the remaining freedom `(r, u, b)` is recovered from the
polynomial itself, which is what makes the parameter map injective. A square difference of two
lifted polynomials therefore has all four coordinates of `s' - s` in `{0, 1}`, so the code
property gives `s = s'`; what is left is a square difference inside `B`, which `B` does not have.
-/

namespace NS

open Polynomial

/-- A parameter tuple `(s, r, u, b)`: a word of the code, the coefficient vector of `R`, a scalar,
and an element of the base. -/
abbrev Param := (Fin 4 → ZMod 3) × (Fin 3 → ZMod 3) × ZMod 3 × (ZMod 3)[X]

/-- The tail of a lifted polynomial, `b + s_∞ T^m + u T^{m+1}`: what the multiplier `Q` acts on. -/
noncomputable def tail (m : ℕ) (p : Param) : (ZMod 3)[X] :=
  p.2.2.2 + C (p.1 3) * X ^ m + C p.2.2.1 * X ^ (m + 1)

/-- The lift of one parameter tuple, `V_s + P·R_r + Q·(b + s_∞ T^m + u T^{m+1})`. -/
noncomputable def liftMap (m : ℕ) (p : Param) : (ZMod 3)[X] :=
  V p.1 + P * R p.2.1 + Q * tail m p

/-- The parameter set `S × F_3^3 × F_3 × B`. -/
noncomputable def params (B : Finset (ZMod 3)[X]) : Finset Param :=
  code ×ˢ ((Finset.univ : Finset (Fin 3 → ZMod 3)) ×ˢ
    ((Finset.univ : Finset (ZMod 3)) ×ˢ B))

/-- The lifted set `L_m(B)`, the image of the parameter set under the lift. -/
noncomputable def lift (m : ℕ) (B : Finset (ZMod 3)[X]) : Finset (ZMod 3)[X] :=
  open scoped Classical in (params B).image (liftMap m)

/-- A tuple is a parameter exactly when its code word and its base element are. -/
theorem mem_params {B : Finset (ZMod 3)[X]} {p : Param} :
    p ∈ params B ↔ p.1 ∈ code ∧ p.2.2.2 ∈ B := by
  simp [params, Finset.mem_product]

/-- There are `810 · |B|` parameter tuples: `10 · 27 · 3` choices besides the base element. -/
theorem params_card (B : Finset (ZMod 3)[X]) : (params B).card = 810 * B.card := by
  rw [params, Finset.card_product, Finset.card_product, Finset.card_product, code_card,
    Finset.card_univ, Finset.card_univ, Fintype.card_fun]
  simp [ZMod.card]
  ring

/-- Membership in the lifted set: the elements of `L_m(B)` are the lifts of parameter tuples. -/
theorem mem_lift {m : ℕ} {B : Finset (ZMod 3)[X]} {f : (ZMod 3)[X]} :
    f ∈ lift m B ↔ ∃ p ∈ params B, liftMap m p = f := by
  classical
  simp [lift, Finset.mem_image]

/-- The degree bound: a lift of a tuple whose base element has degree below `m` has degree below
`m + 8`. -/
theorem liftMap_below (m : ℕ) {p : Param} (hb : Below m p.2.2.2) :
    Below (m + 8) (liftMap m p) := by
  have h1 : Below (m + 8) (V p.1 + P * R p.2.1) :=
    Below.mono (by omega) (below_of_degree_le (m := 5) (degree_V_add_P_mul_R_le p.1 p.2.1))
  have h2 : Below (m + 2) (tail m p) := by
    unfold tail
    exact ((hb.mono (by omega)).add (below_C_mul_X_pow _ m (m + 2) (by omega))).add
      (below_C_mul_X_pow _ (m + 1) (m + 2) (by omega))
  have h3 : Below (m + 8) (Q * tail m p) := by
    have h4 := h2.Q_mul
    rwa [show m + 2 + 6 = m + 8 from by omega] at h4
  exact h1.add h3

/-- The value of a lifted polynomial at `0` is the code coordinate `s_0`. -/
theorem eval_liftMap_zero (m : ℕ) (p : Param) : (liftMap m p).eval 0 = p.1 0 := by
  simp [liftMap, eval_P, eval_Q, eval_V_zero]

/-- The value of a lifted polynomial at `1` is the code coordinate `s_1`. -/
theorem eval_liftMap_one (m : ℕ) (p : Param) : (liftMap m p).eval 1 = p.1 1 := by
  simp [liftMap, eval_P, eval_Q, eval_V_one]

/-- The value of a lifted polynomial at `2` is the code coordinate `s_2`. -/
theorem eval_liftMap_two (m : ℕ) (p : Param) : (liftMap m p).eval 2 = p.1 2 := by
  simp [liftMap, eval_P, eval_Q, eval_V_two]

/-- **The top coordinate.** When the base element has degree below `m`, the coefficient of a
lifted polynomial at `T^{m+6}` is the code coordinate `s_∞`: the part `V_s + P·R_r` has degree at
most `5 < m + 6`; `Q · b` has degree below `m + 6`; `Q · s_∞ T^m` contributes `s_∞` times the
leading coefficient of `Q`; and `Q · u T^{m+1}` would contribute `u` times the vanishing
coefficient `[T^5] Q`. -/
theorem coeff_liftMap_top (m : ℕ) {p : Param} (hb : Below m p.2.2.2) :
    (liftMap m p).coeff (m + 6) = p.1 3 := by
  sorry

/-- **Injectivity of the lift on parameters.** Two tuples with base elements of degree below `m`
that lift to the same polynomial are equal. No division algorithm is needed: equal outputs give
`(V_s + P·R_r) - (V_s' + P·R_r') = Q · (tail' - tail)`, whose left side has degree below `6`, so
both sides vanish; evaluating at `0, 1, 2` identifies the code words, cancelling `P` identifies
`r`, and comparing the coefficients at `T^m` and `T^{m+1}` identifies `u` and `b`. -/
theorem liftMap_injOn (m : ℕ) (B : Finset (ZMod 3)[X]) (hB : AllBelow m B) :
    Set.InjOn (liftMap m) (params B) := by
  sorry

/-- The lift multiplies cardinality by `810`. -/
theorem lift_card (m : ℕ) (B : Finset (ZMod 3)[X]) (hB : AllBelow m B) :
    (lift m B).card = 810 * B.card := by
  classical
  rw [lift, Finset.card_image_of_injOn (liftMap_injOn m B hB), params_card]

/-- The lift of a set of polynomials of degree below `m` has degree below `m + 8`. -/
theorem lift_allBelow (m : ℕ) (B : Finset (ZMod 3)[X]) (hB : AllBelow m B) :
    AllBelow (m + 8) (lift m B) := by
  intro f hf
  obtain ⟨p, hp, rfl⟩ := mem_lift.mp hf
  exact liftMap_below m (hB _ (mem_params.mp hp).2)

/-- **The lift preserves square-difference-freeness** for even `m`. If two lifted polynomials
differ by `z^2`, then the four coordinates of `s' - s` are squares in `F_3`, hence in `{0, 1}`,
so the code property gives `s = s'`; then `z` vanishes on `F_3`, so `z = P·w`, the parts below
`Q` cancel, and `w^2 = (b' - b) + (u' - u) T^{m+1}`. A nonzero square has even natural degree,
while `m + 1` is odd, so `u' = u`; and `w^2 = b' - b` forces `w = 0` because `B` is
square-difference-free. -/
theorem lift_sdf (m : ℕ) (B : Finset (ZMod 3)[X]) (hm : Even m) (hB : AllBelow m B)
    (hS : SDF B) : SDF (lift m B) := by
  sorry

end NS
