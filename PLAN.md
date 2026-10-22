# PLAN: Lean proof of "one of ζ(7), ζ(9), …, ζ(21) is irrational" (instance Z7)

Started 2026-10-21. Mathematical source: `../handoff/zeta7/PROOF_ZETA.md` (instance Z7, §9). Template:
`../lean_beta/` (β(4..36), same toolchain). Labels as in `math/CLAUDE.md`.

## Status: COMPLETE (2026-10-22)

`ZetaIrr.Z7.oneOfZeta7To21 : OneOfZeta7To21` is proved; `lake env lean Axioms.lean` prints only
`[propext, Classical.choice, Quot.sound]` for it and every audited ingredient. No `sorry`, `native_decide`,
`axiom` or `implemented_by` in the sources. What remains is outside Lean: a human/expert read, and the publication
decision (license, push). The rest of this file is the development record.

## Target

```lean
theorem ZetaIrr.Z7.oneOfZeta7To21 : OneOfZeta7To21
-- OneOfZeta7To21 := ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), Irrational (riemannZeta j).re
```

Standard axioms only, no `sorry`, no `native_decide`, all certificates `decide +kernel`.

## Architecture (mirrors lean_beta)

| piece | file(s) | status |
|---|---|---|
| ζ(s) as a real series, link to `riemannZeta` | `Defs.lean` | done |
| statement, reduction to small forms | `Statement.lean`, `Criterion.lean` | done |
| Z7 parameters, `R`, `L`, `Hyp`, `oneOfZeta7To21_of_hyp` | `FamilyZ7.lean` | done |
| Lemmas 1–3 for partial-fraction data (integer poles, 4th derivative, ζ(i+4)) | `Expansion.lean` | done |
| Z7 partial-fraction data (definitions) | `Z7/Concrete/Data.lean` | done |
| copied generic infrastructure (namespace `ZetaIrr`) | `PNT/`, `Stirling/`, `Interval/`, `Analytic/`, `Arith/{Valuation,PSVal,Legendre}`, `Concrete/PartialFrac`, `Fam/`, `Size/`, `Assembly` | copied from lean_beta (docstrings still cite PROOF_BETA) |
| W1: Lemma 3 for Z7, Lemma 4, Lemma 5 glue | `Z7/Concrete/`, `Z7/Arith/`, `Arith/` (new files), `Z7/Glue/` | **done** |
| W2: A-certificate (spec, soundness, kernel computation) | `Z7/CertA/`, `Z7/CertAK/`, `scripts/certA/` | **done** (`bodyUnits_400`) |
| W3: contour, Γ-form, Laplace; Lemma 6(i) and 6(ii) from `SaddleData` | `Analytic/` (new files), `Stirling/`, `Z7/Analytic/` | **done** (`size_of_saddleData`, `nonvan_of_saddleData`) |
| Lemma 6 for Z7, unconditional | `Z7/Lemma6.lean` (`size_Z7`, `nonvan_Z7`) | **done** |
| W4: kernel-checked saddle certificate | `Interval/`, `Fam/Interval/`, `Z7/Interval/`, `scripts/saddle/` | **done** (`Z7.Interval.Z7_saddleData`, standard axioms; verified by main) |
| main assembly + audit | `Z7/MainCond.lean`, `Z7/MainUnconditional.lean`, `Axioms.lean` | **done** |

## Z7 data

r = 11/12, q = 240, n = nOf m = 240(m+1); rn = 220(m+1), (1+r)n = 460(m+1); blocks (k, 1), k = 1..18,
δ = k/80, δn = 3k(m+1); S = 18, G = 547/120, N = 21, e = 1 (factor 2t + n), ε = (−1)^{rn} = +1.
deg R = −1094(m+1) − 17 (odd). Zeros: l ∈ [1, rn] and −l with l ∈ [n+1, (1+r)n], multiplicity 5. Poles at −k,
k ∈ [3(m+1), n − 3(m+1)] (never at 0, so `R` is smooth on `t > −3(m+1)`; `L m = Σ' t, R⁗(t+1)`).
`𝒩 = (2+r)n + 1 = 700(m+1) + 1`.

Certified numbers (PROOF_ZETA §9):
- A_cert = 11757994664484187722611840743096153/1185451381619680151243401356902400 ≈ 9.9185803 (X = 400,
  30,971 events; `handoff/zeta7/f4_certA_exact.py`, `f4_final.log`).
- Re Ω ≤ −10.1167485; `Vcert = −101167/10000` is used in `Hyp.size`. Q ≤ −0.1981.
- x₀ ≈ 0.8921643 + 0.1829121i, κ = 28.31, M = 301.4, ρ = 0.04614, η_far = 2.63e−2, (S4) a = 9.48e−2, η = 1.210,
  (S5) gap 0.8265 at x_c = 0.8174, sin(240·Im Ω) = −0.932453 (`handoff/zeta7/f5_saddle_cert.jsonl`, last r = 11/12
  entry with 18 blocks).

## Key simplification for the analytic part (W3)

The contour formula gives `L_n = −(1/2πi)∫_{c−i∞}^{c+i∞} R⁗(z) k(z) dz` with `k(z) = π cot(πz)`, `c` a
half-integer in `(0, rn+1)`. Integrate by parts four times on the line: with
`W := R‴k − R″k′ + R′k″ − Rk‴`, `W′ = R⁗k − Rk⁗`, and `W(c+iy) → 0` as `|y| → ∞` (`k⁽ʲ⁾` is bounded on
`Re z = c`, `R⁽ʲ⁾ = O(|z|⁻²)`), so `∫_line R⁗k = ∫_line R k⁗`. Then the trigonometric identity
(checked numerically, provable by `field_simp`/`ring` from `k⁗ = 8π⁵ cos(πz)(cos²(πz) + 2)/sin⁵(πz)`)

    sin⁵(u) · cot⁗(u) = 2 cos 3u + 22 cos u

and the Γ-form `R_n(z) = (2z+n) E_n(z) sin⁵(πz)/π⁵` (ε = +1) give the **entire-in-the-trig-part integrand**

    G_n(z) := R_n(z) k⁗(z) = (2z + n) · E_n(z) · T(z),     T(z) := 2 cos(3πz) + 22 cos(πz),

with `T(z) = e^{−3πiz}(1 + 11q + 11q² + q³)`, `q = e^{2πiz}`, `|T(z)| ≤ 24 e^{3π Im z}` for `Im z ≥ 0`. So:
* no boundary term `−R‴(c)` (PROOF_ZETA 6.6.0 is replaced by this exact identity);
* no Faà di Bruno, no ψ″, ψ‴: only `log Γ` Stirling is needed for the integrand;
* phase `f(x) = Ψ(x) − 3πi x`, main term on the disc `(2x+1) n · e^{ψ₀(x)} e^{n f(x)} (1 + O(q) + O(1/n))`.
`L_n = −(1/π) Im J_n`, `J_n = i ∫_0^∞ G_n(c + iy) dy` exactly as in lean_beta (`L_eq_J`), and `J_n` is deformed
onto the polyline. The size bound (Lemma 6(i)) also comes from this decomposition (|L| ≤ |J|/π), since the
real-axis route of lean_beta is too weak for Z7 (V_up ≈ −8.92 vs A ≈ 9.92).

Factor list (40 Γ-factors `(c, s, u, β)`, `α = s x + u`): `(5, +1, 0, 0)`, `(5, −1, 11/12, 1)`,
`(5, +1, 23/12, 1)`, `(−5, +1, 1, 1)`, and per block k = 1..18: `(1, +1, k/80, 0)`, `(−1, +1, 1 − k/80, 1)`.
Σ c s = 0, Σ c u = −G = −547/120, Σ c (β − ½) = −18 = −S, Σ c = 10 (so `λ_n = −Gn log n + Gn − 18 log n + 5 log 2π`).
Note β = 0 occurs (lean_beta's `stirling_scaled` assumes β ∈ (0, 2]; generalise to [0, 2] or shift).

## Arithmetic (W1/W2), PROOF_ZETA §3–§5

E_p = 0 for p > n (Lemma A(a) + Lemma B). For √𝒩 < p ≤ n: E_p = max(0, max_{k: B_k ≥ 1} e_p(k)) with
e_p(k) = B_k + 4 − c_p(k) + P_p(k) if k ≥ p; B_k − 1 − c_p(k) + P_p(k) if k < p and P_p(k) ≥ 1; 0 if k < p and
P_p(k) = 0 (Lemma A(b′), new). For p ≤ √𝒩: E_p = max_k(−ν_p(k)) + 2(S+4)(λ_p+1) (no special p = 2). Bracket of
§5.1: c(y) = 5(⌊y+rx⌋ − ⌊y⌋) + 5(⌈y−x⌉ − ⌈y−(1+r)x⌉); tail (S+15)/X + G/(2(X−1)), X = 400. The Lean A value
must reproduce A_cert above (or be slightly larger and still give Q < 0).

## Rules for workstreams

1. Work only in your own folders (table above). Do not edit files you do not own; if a generic file needs a
   ζ variant, create a new file next to it (e.g. `Analytic/ContourCot.lean`). Owners of copied generic folders:
   `Stirling/`, `Analytic/` → W3; `Interval/`, `Fam/Interval/` → W4; `Arith/`, `Concrete/` → W1. The main session
   owns `Defs`, `Statement`, `Criterion`, `Assembly`, `FamilyZ7`, `Expansion`, `Z7/Concrete/Data.lean`,
   `ZetaIrrational.lean`, `Axioms.lean`, README/TRUST/PLAN. Ask (SendMessage to the main session) if an
   interface file must change.
2. No `sorry` in delivered files (a `*WIP.lean` file not imported anywhere is fine), no `axiom`, **no
   `native_decide`**. Computations by `decide +kernel`.
3. Every file starts with a docstring: what it proves, the PROOF_ZETA section, `Status:`.
4. Build: `export PATH="$HOME/.elan/bin:$PATH"; LEAN_NUM_THREADS=8 lake build ZetaIrrational.<Module>` from
   `lean_zeta7/` (without the thread cap, ~32 parallel Lean processes fail on Windows with "failed to read file
   ….olean"). Long builds in
   the background with output to a log file under your scratch dir. Do not run a bare `lake build` (the main session
   does full builds). At most one heavy build at a time per workstream (memory: 32 GB shared by all).
5. Check axioms with a scratch file outside the repo (`lake env lean scratch.lean` with `#print axioms`). Expected:
   `[propext, Classical.choice, Quot.sound]`.
6. Commit only your own files: `git add <explicit paths>` (never `-A`), clear message ending with the
   `Co-Authored-By` line; if `.git/index.lock` exists, wait and retry. Push nothing.
7. If a step of PROOF_ZETA does not formalise as written, record the exact gap in `NOTES_FOR_THREAD_F.md`
   (append a section) and tell the main session. Never edit files under `../handoff/` or `../lean_beta/`.

## Progress log

- 2026-10-21: project set up (toolchain, Mathlib v4.35.0 copied from lean_beta's `.lake/packages`); generic
  infrastructure copied; `Defs`, `Statement`, `FamilyZ7` (with `Hyp` and `oneOfZeta7To21_of_hyp`), `Expansion`,
  `Z7/Concrete/Data` written; base built, axiom audit standard, committed (77bb872). Workstreams W1–W4 started.
- 2026-10-22: W4 done (`8582083`, `1d7d722`): `Z7_saddleData : Z7.Analytic.SaddleData`, all `decide +kernel`.
  Re Ω ∈ [−10.1167486, −10.1167485], sin(240 Im Ω) < −0.9, η_far ≈ 0.0199, ρ = 1/20, K ≥ 28, M ≤ 311, sectors
  |α| ≥ 1/100, |arg α| ≤ 2.76; top ray Im Ψ′ ≥ 12 from x_top ≈ 2.0512 + 12.0012i. Interval phase is now a parameter
  ω (`fL ω l z = Ψ(z) − ωπi z`). Build ≈ 4.5 min wall at LEAN_NUM_THREADS=8. Main re-ran the build and audit.
- 2026-10-22: W3 done (`350d939`, `81918a6`, `8330ad0`, `12b8d69`): cot-kernel contour formula, 4-fold by-parts on
  the line, integrand (2z+n)E_n T, Laplace, size via Stirling upper bound for log n!. Stirling generalised to
  β ∈ [0, 2]. Main added `Z7/Lemma6.lean` (`size_Z7`, `nonvan_Z7`, no hypotheses), root import and audit: standard
  axioms only. Remaining: W1 (Lemma 4 + glue) and W2 (A-certificate).
- 2026-10-22: W1 done (`f5ac8a8`, `f49f781`, `b5dd18a`): expansion_Z7, Lemma A/B (with (b′) as `a_int_of_nodvd`),
  Lemma 4, PNT step, glue `oneOfZeta7To21_of_parts`. Main added `Z7/MainCond.lean`:
  `oneOfZeta7To21_of_certUnits : CertA.UnitsFact → OneOfZeta7To21`, standard axioms only. The unit count
  778841997893779320302794447562 · 2⁻⁹⁶ + tail equals Acert exactly. Remaining: W2's kernel run `bodyUnits_400`.
- 2026-10-22: W2 done (`9815d5f`, `5c3c524`): A-certificate spec and soundness, kernel run
  `bodyUnits_400 = 778841997893779320302794447562` (30,137 intervals, 1,029 chunks; ~29 min wall at
  LEAN_NUM_THREADS=12, ~3.3 CPU-h). **Main theorem assembled** (`Z7/MainUnconditional.lean`): full `lake build` OK,
  axiom audit standard. Unused copied `Size/` and coordination marker files removed; README/TRUST final.
