# One of ζ(7), ζ(9), …, ζ(21) is irrational: a Lean 4 proof

This repository contains a machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the following theorem.

> **Theorem.** At least one of the eight numbers ζ(7), ζ(9), ζ(11), …, ζ(21) is irrational.

In Lean:

```lean
-- ZetaIrrational/Statement.lean
def OneOfZeta7To21 : Prop :=
  ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), Irrational (riemannZeta j).re

-- ZetaIrrational/Z7/MainUnconditional.lean
theorem ZetaIrr.Z7.oneOfZeta7To21 : OneOfZeta7To21
```

```
'ZetaIrr.Z7.oneOfZeta7To21' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`riemannZeta` is Mathlib's Riemann zeta function. The proof uses only Lean's three standard axioms: no `sorry`, no
added `axiom`, no `native_decide`; every numerical certificate is evaluated by the Lean kernel. See [TRUST.md](TRUST.md).

For comparison: Zudilin (Izv. Math. 66 (2002)) proved "one of ζ(7), …, ζ(37)"; Lai–Zhou (Publ. Math. Debrecen 101
(2022)) proved "two of ζ(5), …, ζ(35)", which implies "one of ζ(7), …, ζ(35)". The namespace `Z7` names the parameter
set of the informal proof (`handoff/zeta7/PROOF_ZETA.md` §9).

## Outline of the proof

For n ∈ 240ℕ let

    R_n(t) = (2t + n) · Π_{l=1}^{rn} (t − l)⁵ · Π_{l=n+1}^{(1+r)n} (t + l)⁵ / Π_{j=1}^{18} Π_{k=jn/80}^{n−jn/80} (t + k)

with r = 11/12, and L_n = Σ_{t ≥ 1} R_n⁗(t).

1. **No ζ(3), ζ(5), no even values (Lemmas 1–3).** L_n ∈ ℚ + ℚζ(7) + ℚζ(9) + … + ℚζ(21): the fourth derivative
   shifts the partial-fraction exponents by 4, the mirror symmetry t ↦ −n−t kills the even indices, and deg R_n ≤ −2
   kills the coefficient of ζ(5). Files: `Expansion.lean`, `Z7/Concrete/`.
2. **Denominators (Lemmas 4–5).** An explicit D_n makes D_n L_n an integer linear form, with
   log D_n ≤ G log n! + nA + o(n), G = 547/120, A ≤ 9.9185803. A is an integral of a step function over the prime
   ranges; its bound is an exact rational certificate (30,137 event intervals) checked in the kernel; the prime number
   theorem passes from primes to the integral. Files: `Z7/Arith/`, `Z7/CertA/`, `Z7/CertAK/`, `Z7/Glue/`, `PNT/`.
3. **Size and nonvanishing (Lemma 6).** L_n is a contour integral of R_n⁗(z)·π cot(πz). Integrating by parts four
   times and using sin⁵u · cot⁗u = 2cos 3u + 22cos u turns the integrand into (2z+n)·E_n(z)·(2cos 3πz + 22cos πz),
   E_n a product of Γ-factors. Uniform complex Stirling and Laplace's method along a certified steepest-descent path
   give log|L_n| ≤ −G log n! + n Re Ω + o(n) with Re Ω ≤ −10.1167485, and L_n ≠ 0 for infinitely many n (the phase
   moves by 240·Im Ω, with sin(240 Im Ω) ≈ −0.932, between consecutive n). The saddle point, the path and all bounds
   along it are certified by kernel-checked interval arithmetic. Files: `Analytic/`, `Stirling/`, `Z7/Analytic/`,
   `Interval/`, `Z7/Interval/`, `Z7/Lemma6.lean`.
4. **Conclusion.** Q = Re Ω + A ≈ −0.198 < 0, so D_n L_n → 0. If ζ(7), …, ζ(21) were all rational, D_n L_n would be
   integers after clearing one fixed denominator, nonzero infinitely often: a contradiction. Files: `Criterion.lean`,
   `Statement.lean`, `FamilyZ7.lean`, `Z7/MainCond.lean`, `Z7/MainUnconditional.lean`.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get                        # download prebuilt Mathlib
LEAN_NUM_THREADS=12 lake build            # about 50 min on a 32-core desktop; the A-certificate dominates
lake env lean Axioms.lean                 # print the axioms of the main theorem and its ingredients
```

On Windows keep `LEAN_NUM_THREADS` at 8–12 (see TRUST.md).

## Repository layout

| path (under `ZetaIrrational/`) | content |
|---|---|
| `Defs.lean`, `Statement.lean`, `Criterion.lean`, `Assembly.lean` | ζ as a real series, the target statement, the irrationality criterion, D_n L_n → 0 |
| `FamilyZ7.lean` | the parameters, the concrete R_n and L_n, and the assembly from the inputs (`Hyp`) |
| `Expansion.lean`, `Concrete/` | Lemmas 1–3 for partial-fraction data; general partial fractions |
| `Arith/`, `Z7/Arith/` | p-adic valuations of power-series coefficients, Legendre, Lemmas A, B, 4 |
| `Z7/CertA/`, `Z7/CertAK/`, `Z7/Glue/`, `PNT/` | Lemma 5: the A-certificate (mathematics in `CertA`, kernel computation in `CertAK`), the PNT step |
| `Analytic/`, `Stirling/`, `Fam/Analytic/`, `Z7/Analytic/` | cot-kernel contour formula, integration by parts, Γ-form, complex Stirling, Laplace, Lemma 6 from saddle data |
| `Interval/`, `Fam/Interval/`, `Z7/Interval/` | rational interval and complex-box arithmetic; the kernel-checked saddle certificate |
| `Z7/Lemma6.lean`, `Z7/MainCond.lean`, `Z7/MainUnconditional.lean` | the final assembly |
| `../scripts/` | generators for the certificate data (untrusted; see TRUST.md) |
| `../Axioms.lean` | axiom audit |

Every Lean file starts with a docstring saying what it proves and its status. References such as "PROOF_ZETA §5"
point to the informal write-up (`handoff/zeta7/PROOF_ZETA.md` in the parent project). The instance-independent
infrastructure (PNT port, Stirling, interval arithmetic, contour and Laplace lemmas, partial fractions, valuations)
is adapted from the β(4..36) formalisation `lean_beta`; those files still cite `PROOF_BETA` sections.

## Status and caveats

- The Lean kernel has checked the proof. **No human expert has yet reviewed the mathematics or the Lean code.** The
  statement (see TRUST.md) is one line and worth reading.
- The construction, the proofs, the parameter search, the certificate programs and the Lean formalisation were produced
  largely by AI models (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel check,
  all verification so far has been done by AI systems.
- The margin is Q ≈ −0.198; it is certified, not estimated.

## Acknowledgements

- `PNT/Port/` is ported from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (A. Kontorovich, T. Tao et al.), via the port in [domino14/zeta5](https://github.com/domino14/zeta5), under the
  Apache License 2.0 (see `PNT/Port/LICENSE`).
- The construction builds on T. Rivoal (C. R. Acad. Sci. 2000; Acta Arith. 103, 2002), T. Rivoal and W. Zudilin
  (Math. Ann. 326, 2003), W. Zudilin (Izv. Math. 66, 2002; J. Théor. Nombres Bordeaux 16, 2004), and X. Lai and
  L. Zhou (Publ. Math. Debrecen 101, 2022).

## License

No license file yet; `lean_beta` is Apache-2.0 and `PNT/Port/` carries its own Apache-2.0 `LICENSE`. The author decides
before publishing.
