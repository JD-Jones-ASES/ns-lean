# Verification

All six statements of Challenge.lean have proofs. The local build, the axiom audit, the source
guard and the standard-library cross-check pass.

## Formal scope

| Statement | Proved in |
| --- | --- |
| `NS.D3_8_ge_810` — 810 elements in `P_{3,8}` | NS/Main.lean |
| `NS.conjecture13_fails_3_2_8` — the bound fails at `n = 8` | NS/Main.lean |
| `NS.D3_8e_ge` — `810^e` in `P_{3,8e}` | NS/Main.lean |
| `NS.D3_8e4_ge` — `27 · 810^e` in `P_{3,8e+4}` | NS/Main.lean |
| `NS.conjecture13_fails_3_2_all` — the bound fails at every `n ≡ 0 (mod 4)`, `n ≥ 8` | NS/Main.lean |
| `NS.liminf_ge` — `16/21 ≤ liminf log D_3(n) / (n log 3)` | NS/Asymptotics.lean |

Each is restated verbatim in Solution.lean. The lift itself is NS/Lift.lean, the two bases
NS/Bases.lean and the two inductions NS/Families.lean; PROOF.md names the lemma behind each step.

## Local checks

```sh
lake build
python scripts/check-source.py
python scripts/check_construction.py
```

The `Test` target audits every constant in the `NS` namespace and its private auxiliaries (the
declarations of the sources and the constants Lean generates for them; 188 at the time of writing,
floor 180), permits only `propext`, `Classical.choice` and `Quot.sound`, and fails if any of the
six compared theorems is missing. A placeholder in a proof compiles with a warning; this audit is
what fails the build. Challenge.lean intentionally contains six proof placeholders; Solution.lean
and the modules it imports contain none, and Solution.lean does not import Challenge.lean. The
source guard rejects `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `native_decide`,
`implemented_by`, `extern`, `Lean.ofReduceBool` and the kernel-bypass options in `NS/`,
Solution.lean and `Test/`, the same tokens except `sorry` in Challenge.lean, and any `debug.`
option in lakefile.toml. There is no `native_decide`; the largest kernel computations are the code
property, decided over all 100 ordered pairs of words, and the comparison `3^128 ≤ 810^21` by
`norm_num`.

Lean 4.33.0 and Mathlib v4.33.0 (commit `db584cd6d46c92f209a44c0f1c829460d327499d`) are pinned by
the committed manifest; `lake update` is never run.

## Controls

Each of these edits, made in a scratch copy, breaks the build as it must: a word of the code
replaced by `0011` (the `decide` in `code_property` reports the proposition false); `Even m`
dropped from `lift_sdf` and `AllBelow m B` from `lift_card` (the proofs fail; at `m = 1` the lift
has 2511 square differences, and with `B = {0, T^{m+1}}` it has 810 elements, not 1620); a `sorry`
in a proved lemma of NS/Lift.lean (compiles through Solution.lean, caught by the axiom audit and
the source guard); `810` replaced by `811` in `fam0_card`; `16/21` replaced by `17/21` in the
internal liminf statement (the final comparison fails); a declared `axiom` and a `native_decide`
(both surface in the audit).

`scripts/check_construction.py` rebuilds the code, the two bases and the lifted sets with the
standard library and exact integers, and ends:

```text
control: the code with 2221 replaced by 1111 fails the code property, as it must
control: the set {0, 1} of polynomials of degree below 2 has the square difference 1 = 1^2, as it must
ALL CHECKS PASSED
```

## Not checked here

- Optimality: the ten-word code is not claimed to be largest, and no lift is claimed to be best.
- Values: no value of `D_3(n)` is determined and no upper bound on `D_3(n)` is proved, at `n = 4`
  or anywhere else.
- Other fields: nothing is claimed at any `q` other than 3, and Naslund's Theorem 1 is not
  formalized.
- The Python script is a cross-check of finite instances, not a premise of any Lean proof.
