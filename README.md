# lean_zeta7 — Lean 4 + Mathlib formalisation of "one of ζ(7), ζ(9), …, ζ(21) is irrational"

Target theorem (standard axioms only, no `sorry`, no `native_decide`):

```lean
-- ZetaIrrational/Statement.lean
def OneOfZeta7To21 : Prop :=
  ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), Irrational (riemannZeta j).re

-- to be assembled in ZetaIrrational/Z7/MainUnconditional.lean
theorem ZetaIrr.Z7.oneOfZeta7To21 : OneOfZeta7To21
```

Source mathematics: `../handoff/zeta7/PROOF_ZETA.md` (instance Z7: r = 11/12, 18 pole blocks at δ = k/80, q = 240,
certified Q ≤ −0.1981). Template: `../lean_beta/` (the β(4..36) formalisation, same toolchain, Lean/Mathlib v4.35.0);
its instance-independent infrastructure (PNT port, complex Stirling, interval arithmetic, contour/Laplace lemmas,
partial fractions, p-adic valuations) is copied here with the namespace renamed to `ZetaIrr`. Those files still cite
`PROOF_BETA` sections in their docstrings.

**Status: work in progress.** See [PLAN.md](PLAN.md) for what is done and what is open, and [TRUST.md](TRUST.md) for
what a reader has to trust.

## Building

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get          # prebuilt Mathlib
lake build
lake env lean Axioms.lean   # axiom audit
```

## Outline

For n ∈ 240ℕ let

    R_n(t) = (2t + n) · Π_{l=1}^{rn} (t − l)⁵ · Π_{l=n+1}^{(1+r)n} (t + l)⁵ / Π_j Π_{k=δ_j n}^{(1−δ_j)n} (t + k),

r = 11/12, δ_j = j/80 (j = 1, …, 18), and L_n = Σ_{t ≥ 1} R_n⁗(t).
1. Lemmas 1–3 (`Expansion.lean`, `Z7/Concrete/`): L_n ∈ ℚ + ℚζ(7) + ℚζ(9) + … + ℚζ(21).
2. Lemmas 4–5 (`Z7/Arith/`, `Z7/CertA/`, `Z7/CertAK/`, `Z7/Glue/`, `PNT/`): a denominator D_n with
   log D_n ≤ G log n! + nA + o(n), A ≤ 9.9185803 (exact-rational certificate checked by the kernel).
3. Lemma 6 (`Z7/Analytic/`, `Z7/Interval/`): a contour integral deformed through a certified saddle point gives
   log |L_n| ≤ −G log n! + n Re Ω + o(n) with Re Ω ≤ −10.1167485, and L_n ≠ 0 for infinitely many n.
4. Q = Re Ω + A < 0, so D_n L_n → 0 while being a nonzero integer infinitely often (after clearing one fixed
   denominator) if all of ζ(7), …, ζ(21) were rational.
