# One of ζ(7), ζ(9), …, ζ(21) is irrational: a Lean 4 proof

This repository contains a complete, machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the following theorem.

> **Theorem.** At least one of the eight numbers ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21) is irrational.

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

`riemannZeta` is Mathlib's Riemann zeta function and `Irrational` is Mathlib's. The proof uses only Lean's three
standard axioms. There is no `sorry`, no added `axiom` and no `native_decide`: every numerical certificate is evaluated
by the Lean kernel. See [TRUST.md](TRUST.md) for what a reader has to trust.

## Context

Ball and Rivoal (2001) showed that infinitely many of the numbers ζ(2k+1) are irrational. Rivoal (2002) proved that one
of ζ(5), …, ζ(21) is irrational, and Zudilin (Russian Math. Surveys 56, 2001) that one of ζ(5), ζ(7), ζ(9), ζ(11) is.
Windows that also exclude ζ(5) are wider. Zudilin (Izv. Math. 66, 2002) proved that one of ζ(7), …, ζ(37) is
irrational. Lai and Zhou (Publ. Math. Debrecen 101, 2022) proved that two of ζ(5), …, ζ(35) are, which gives one of
ζ(7), …, ζ(35).

The theorem here narrows that window to ζ(7), …, ζ(21). Its linear forms never involve ζ(3) or ζ(5), and nothing about
those two numbers is assumed. These are the closest published results we know of; we have not run a systematic search
(e.g. of MathSciNet or zbMATH), so please tell us if you know of prior work.

## The construction

Fix r = 11/12 and the eighteen offsets δ_j = j/80 (j = 1, …, 18). For n ∈ 240ℕ put

    R_n(t) = (2t + n) · Π_{l=1}^{rn} (t − l)⁵ · Π_{l=n+1}^{(1+r)n} (t + l)⁵  /  Π_{j=1}^{18} Π_{k=δ_j n}^{(1−δ_j) n} (t + k),

    L_n = Σ_{t ≥ 1} R_n⁗(t).

R_n has zeros of order 5 at 1, …, rn and at −n−1, …, −(1+r)n, and poles at −k for δ_1 n ≤ k ≤ (1 − δ_1) n, of order
B_k ≤ 18 (the number of blocks containing k). Its degree is −Gn − 17, where G = Σ_j (1 − 2δ_j) − 10r = 547/120. In Lean
these are `ZetaIrr.Z7.R`, `ZetaIrr.Z7.L` (`FamilyZ7.lean`), with n = 240(m+1); the namespace `Z7` is the name of this
parameter set.

## Outline of the proof

1. **Lemmas 1–3 (L_n is a linear form in ζ(7), …, ζ(21)).** Write R_n = Σ_k Σ_i a_{i,k}(t+k)^{−i} in partial fractions.
   - Lemma 1: since Σ_{t≥1}(t+k)^{−j} = ζ(j) − H_k^{(j)}, L_n = ρ_n + Σ_i i(i+1)(i+2)(i+3) τ_i ζ(i+4), with
     ρ_n ∈ ℚ and τ_i = Σ_k a_{i,k}.
   - Lemma 2: R_n(−n−t) = −R_n(t) (the degree is odd), so τ_i = 0 for even i.
   - Lemma 3: τ_1 = 0 because deg R_n ≤ −2, so ζ(5) does not occur, and i ≤ 18 leaves ζ(7), ζ(9), …, ζ(21).

   Files: `Expansion.lean`, `Concrete/`, `Z7/Concrete/`.
2. **Lemma 4 (denominators).** An explicit D_n = Π_{p ≤ n} p^{E_p} makes D_n ρ_n and all D_n τ_i integers. The
   exponents come from the p-adic valuations of the Taylor coefficients at each pole (Lemma A) and of the harmonic
   sums H_k^{(j)} (Lemma B). E_p = 0 for p > n; for √𝒩 < p ≤ n, with 𝒩 = (2 + r)n + 1, E_p is an explicit count of
   multiples of p among the zeros and poles; for smaller p a crude bound suffices.
   Files: `Arith/`, `Z7/Arith/`.
3. **Lemma 5 (size of D_n).** log D_n ≤ G log n! + nA + o(n) with A ≤ 9.9185803. For √𝒩 < p ≤ n,
   E_p − G⌊n/p⌋ ≤ e*(n/p) for an explicit step function e*, so the prime sum is n∫e*(x) dx/x² + o(n) by the prime
   number theorem. The integral over [1, 400] is an exact rational certificate on 30,137 intervals, checked by the
   kernel; the rest is bounded by 33/400 + G/798.
   Files: `Z7/CertA/` (the mathematics), `Z7/CertAK/` (the kernel computation), `Z7/Glue/`, `PNT/`.
4. **Lemma 6 (size and nonvanishing of L_n).**
   - L_n is a contour integral of R_n⁗(z)·π cot(πz) over a vertical line. Integrating by parts four times and using
     sin⁵u · cot⁗u = 2 cos 3u + 22 cos u turns the integrand into (2z + n)·E_n(z)·(2 cos 3πz + 22 cos πz). Here E_n
     is a product of 40 Γ-factors Γ(nα_i(z/n) + β_i)^{c_i}.
   - Uniform complex Stirling bounds show that, along z = nx, the integrand behaves like
     exp(−G log n! + n f(x) + O(log n)), with f(x) = Ψ(x) − 3πix and Ψ(x) = Σ c_i α_i(x) log α_i(x).
   - The contour is deformed onto a steepest-descent path through the saddle point x₀ ≈ 0.8922 + 0.1829i of f, and
     Laplace's method is applied at x₀. This gives (i) log |L_n| ≤ −G log n! + n Re Ω + o(n), where Ω = f(x₀) and
     Re Ω ≤ −10.1167485, and (ii) L_n ≠ 0 for infinitely many n, because the phase advances by 240·Im Ω between
     consecutive admissible n and sin(240·Im Ω) ≈ −0.932 ≠ 0.
   - The saddle point, the path and all bounds along it (conditions (S0)–(S5), `Z7/Analytic/SaddleData.lean`) are
     certified by kernel-checked rational interval arithmetic.

   Files: `Analytic/`, `Stirling/`, `Fam/Analytic/`, `Z7/Analytic/`, `Interval/`, `Fam/Interval/`, `Z7/Interval/`,
   `Z7/Lemma6.lean`.
5. **Conclusion.** Re Ω + A ≈ −0.198 < 0, so D_n L_n → 0. If ζ(7), …, ζ(21) were all rational with common
   denominator Q, the numbers Q·D_n·L_n would be integers, nonzero for infinitely many n by Lemma 6(ii), and tending
   to 0: a contradiction. Files: `Criterion.lean`, `Statement.lean`, `Assembly.lean`, `FamilyZ7.lean`,
   `Z7/MainCond.lean`, `Z7/MainUnconditional.lean`.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get                  # download prebuilt Mathlib
LEAN_NUM_THREADS=12 lake build      # about 50 minutes on a 32-core desktop; the A-certificate dominates
lake env lean Axioms.lean           # print the axioms of the main theorem and its ingredients
```

Building needs at least 16 GB of RAM (more with more threads). On Windows, set `LEAN_NUM_THREADS` to 8–12: with one
job per core, the parallel Lean processes can fail with "failed to read file ….olean" (a resource limit, not a proof
error).

## Repository layout

Paths are relative to `ZetaIrrational/`.

| path | content |
|---|---|
| `Defs.lean`, `Statement.lean` | ζ at integers as a real series (linked to Mathlib's `riemannZeta`), the target statement |
| `Criterion.lean`, `Assembly.lean`, `FamilyZ7.lean` | the irrationality criterion; D_n L_n → 0; the parameters, R_n, L_n and the assembly |
| `Expansion.lean`, `Concrete/`, `Z7/Concrete/` | Lemmas 1–3: partial fractions and the expansion of L_n |
| `Arith/`, `Z7/Arith/` | p-adic valuations, Legendre's formula, Lemmas A, B and 4 |
| `Z7/CertA/`, `Z7/CertAK/`, `Z7/Glue/`, `PNT/` | Lemma 5: the step function e*, the A-certificate and its kernel computation, the prime number theorem step |
| `Analytic/`, `Stirling/`, `Fam/Analytic/`, `Z7/Analytic/` | Lemma 6: contour formula, integration by parts, Γ-form, complex Stirling, deformation, Laplace's method |
| `Interval/`, `Fam/Interval/`, `Z7/Interval/` | rational interval and complex-box arithmetic; the saddle-point certificate |
| `Z7/Lemma6.lean`, `Z7/MainCond.lean`, `Z7/MainUnconditional.lean` | the final assembly |

`scripts/` holds the (untrusted) generators of the certificate data, and `Axioms.lean` is the axiom audit. Every Lean file
starts with a docstring saying what it proves.

## Status and caveats

- The Lean kernel has checked the proof. **No human expert has yet reviewed the mathematics or the Lean code.** The
  statement (see TRUST.md) is one line and worth reading.
- The construction, the proofs, the parameter search, the certificate programs and the Lean formalisation were produced
  largely by AI models (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel check,
  all verification so far has been done by AI systems.
- The numerical margin is Re Ω + A ≈ −0.198. It is certified, not estimated.

## Acknowledgements

- `PNT/Port/` is ported from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (A. Kontorovich, T. Tao et al.), via the port in [domino14/zeta5](https://github.com/domino14/zeta5), under the
  Apache License 2.0 (see `ZetaIrrational/PNT/Port/LICENSE`).
- The method follows K. Ball and T. Rivoal (Invent. Math. 146, 2001), T. Rivoal (Acta Arith. 103, 2002), T. Rivoal
  and W. Zudilin (Math. Ann. 326, 2003), W. Zudilin (Izv. Math. 66, 2002), and X. Lai and L. Zhou (Publ. Math.
  Debrecen 101, 2022).

## License

Apache License 2.0 (see [LICENSE](LICENSE)). `ZetaIrrational/PNT/Port/` is derived from PrimeNumberTheoremAnd, also
Apache-2.0; its own `LICENSE` file and the provenance notes in its file headers are kept.
