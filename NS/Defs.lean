import Mathlib

/-!
# Definitions

The four definitions of `Challenge.lean`, character for character: `SDF`, `DegLT`, `polyLT`, `D3`.
`Solution.lean` proves the statements of `Challenge.lean` about these definitions without
importing `Challenge.lean`.
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

end NS
