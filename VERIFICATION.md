# Verification

All six statements of Challenge.lean have proofs. The local build, the axiom audit over every
declaration, the source guard and the standard-library cross-check pass. No GitHub Actions
minutes were used.

## Formal scope

| Statement | Proof module |
| --- | --- |
| `NS.D3_8_ge_810` — 810 elements in `P_{3,8}` | NS/Main.lean |
| `NS.conjecture13_fails_3_2_8` — the bound fails at `n = 8` | NS/Main.lean |
| `NS.D3_8e_ge` — `810^e` in `P_{3,8e}` | NS/Main.lean |
| `NS.D3_8e4_ge` — `27 · 810^e` in `P_{3,8e+4}` | NS/Main.lean |
| `NS.conjecture13_fails_3_2_all` — the bound fails at every `n ≡ 0 (mod 4)`, `n ≥ 8` | NS/Main.lean |
| `NS.liminf_ge` — `16/21 ≤ liminf log D_3(n) / (n log 3)` | NS/Asymptotics.lean |

The lift itself is NS/Lift.lean, the two bases NS/Bases.lean and the two inductions
NS/Families.lean; PROOF.md names the lemma behind each step.

## Local checks

```sh
lake build
python scripts/check-source.py
python scripts/check_construction.py
```

The build audits DESK_FILLS project declarations, including private ones, with only `propext`,
`Classical.choice` and `Quot.sound` permitted, and fails if any of the six compared theorems is
missing. Challenge.lean intentionally contains six proof placeholders; Solution.lean and the
modules it imports contain none, and Solution.lean does not import Challenge.lean. The source
guard rejects placeholders, added axioms and kernel bypasses. There is no `native_decide`: the
largest kernel computations are the 90-pair code property and the comparison `3^128 ≤ 810^21`.
Definitions, theorem types and proof terms are those of commit DESK_FILLS.

Lean 4.33.0 and Mathlib v4.33.0 (commit `db584cd6d46c92f209a44c0f1c829460d327499d`) are pinned by
the committed manifest; `lake update` is never run.

`scripts/check_construction.py` rebuilds the code, the two bases and the lifted sets with the
standard library and exact integers, and ends:

```text
control: the code with 2221 replaced by 1111 fails the code property, as it must
control: the set {0, 1} of polynomials of degree below 2 has the square difference 1 = 1^2, as it must
ALL CHECKS PASSED
```

## Not checked here

- Optimality: the ten-word code is not claimed to be largest, and no lift is claimed to be best.
- Values: no value of `D_3(n)` is determined, and no upper bound on `D_3(n)` is proved, at `n = 4`
  or anywhere else.
- Other fields: nothing is claimed at any `q` other than 3, and Naslund's Theorem 1 is not
  formalized.
- The Python script is a cross-check of finite instances, not a premise of any Lean proof; the
  Lean development does not read it.
