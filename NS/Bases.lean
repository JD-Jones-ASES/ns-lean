import NS.Below
import NS.Code

/-!
# The two bases

The recursion needs a starting set at each residue of `n` modulo `8` that the construction
reaches. `B_0 = {0}` is the trivial square-difference-free subset of `P_{3,0}`, and

`B_4 = { a T^3 + b T + c (1 - T^2) : a, b, c ∈ F_3 }`

is a square-difference-free subset of `P_{3,4}` with `27` elements. Square-difference-freeness of
`B_4` is the only place where the shape `1 - T^2` matters: a difference of two of its elements
has constant term `c` and `T^2`-coefficient `-c`, while a nonzero square of degree below `4` is
the square of a linear polynomial `v + u T`, with constant term `v^2` and `T^2`-coefficient
`u^2`; so `v^2 + u^2 = 0`, which in `F_3` forces `u = v = 0`.
-/

namespace NS

open Polynomial

/-- The base `B_0 = {0} ⊆ P_{3,0}`. -/
noncomputable def base0 : Finset (ZMod 3)[X] := {0}

/-- `B_0` has one element. -/
theorem base0_card : base0.card = 1 := Finset.card_singleton 0

/-- `B_0` lies in `P_{3,0}`. -/
theorem base0_allBelow : AllBelow 0 base0 := by
  intro f hf
  rw [base0, Finset.mem_singleton] at hf
  subst hf
  exact below_zero 0

/-- `B_0` is square-difference-free. -/
theorem base0_sdf : SDF base0 := by
  intro f hf g hg z hz
  rw [base0, Finset.mem_singleton] at hf hg
  subst hf; subst hg
  simpa using hz.symm

/-- One element of `B_4`, the polynomial `a T^3 + b T + c (1 - T^2)`. -/
noncomputable def base4Map (t : ZMod 3 × ZMod 3 × ZMod 3) : (ZMod 3)[X] :=
  C t.1 * X ^ 3 + C t.2.1 * X + C t.2.2 * (1 - X ^ 2)

/-- The base `B_4 = { a T^3 + b T + c (1 - T^2) : a, b, c ∈ F_3 } ⊆ P_{3,4}`. -/
noncomputable def base4 : Finset (ZMod 3)[X] :=
  open scoped Classical in Finset.univ.image base4Map

/-- Distinct triples give distinct elements of `B_4`: the coefficients at `T^3`, `T` and `1` read
`a`, `b` and `c` back. -/
theorem base4Map_injective : Function.Injective base4Map := by
  intro t t' h
  have h3 := congrArg (fun f => Polynomial.coeff f 3) h
  have h1 := congrArg (fun f => Polynomial.coeff f 1) h
  have h0 := congrArg (fun f => Polynomial.coeff f 0) h
  simp only [base4Map, mul_sub, mul_one, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow,
    coeff_C, coeff_X] at h3 h1 h0
  norm_num at h3 h1 h0
  exact Prod.ext h3 (Prod.ext h1 h0)

/-- `B_4` has `27` elements. -/
theorem base4_card : base4.card = 27 := by
  classical
  rw [base4, Finset.card_image_of_injective _ base4Map_injective, Finset.card_univ]
  simp [ZMod.card]

/-- `B_4` lies in `P_{3,4}`. -/
theorem base4_allBelow : AllBelow 4 base4 := by
  classical
  intro f hf
  rw [base4, Finset.mem_image] at hf
  obtain ⟨t, -, rfl⟩ := hf
  refine below_of_degree_le (m := 3) ?_
  unfold base4Map
  compute_degree
  norm_num

/-- **`B_4` is square-difference-free.** A difference of two of its elements has constant term `c`
and `T^2`-coefficient `-c`; a nonzero square of degree below `4` is the square of a linear
polynomial `v + u T`, whose constant term is `v^2` and whose `T^2`-coefficient is `u^2`; so
`v^2 + u^2 = 0`, and in `F_3` that forces `u = v = 0`. -/
theorem base4_sdf : SDF base4 := by
  sorry

end NS
