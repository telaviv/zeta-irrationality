# Notes for Thread F (`handoff/zeta7/ZETA7.md`) from the Lean formalisation

Findings from `lean_zeta7` that concern the informal proof `handoff/zeta7/PROOF_ZETA.md`. Files under `handoff/`
are not edited from here; these notes are meant to be copied into ZETA7.md by the Thread F session.

## 1. Lemma 6: the boundary term disappears (2026-10-21, main session) [Proved identity; Lean port in progress]

Integrating by parts four times on the vertical line Re z = c (c a half-integer, so k⁽ʲ⁾ is bounded there, and
R⁽ʲ⁾ = O(|z|⁻²)) gives exactly

    ∫_{c−i∞}^{c+i∞} R_n⁗(z) π cot(πz) dz = ∫_{c−i∞}^{c+i∞} R_n(z) k⁗(z) dz,    k(z) = π cot(πz),

and the elementary identity sin⁵(u)·cot⁗(u) = 2cos 3u + 22cos u (= 8 cos u (cos²u + 2)), together with the Γ-form
R_n = ε(2z+n)^e E_n sin⁵(πz)/π⁵, gives

    R_n(z) k⁗(z) = ε (2z+n)^e E_n(z) T(z),    T(z) = 2cos(3πz) + 22cos(πz) = e^{−3πiz}(1 + 11q + 11q² + q³).

So PROOF_ZETA (6.6.0) can be replaced by L_n = −(1/π) Im J_n with J_n = i∫_0^∞ R_n k⁗(c+iy) dy, with no boundary
term −R_n‴(c), no Faà di Bruno form (6.2.1), and no need for Λ_n″, Λ_n‴ in (6.4.2): only log Γ Stirling enters. The
phase is still f = Ψ − 3πix, and the disc amplitude is ε(2x+1)^e n^e e^{ψ₀(x)}(1 + O(q) + O(1/n)) (the factor
(Ψ′(x₀) − 5πi)⁴ = 16π⁴ of (6.5.1) is absorbed: it is the same main term after integration by parts). [Identity
sin⁵·cot⁗ checked numerically to 30 digits at three complex points; the by-parts step is standard.] It also
simplifies §10 item 4 (the near-real-axis piece): T is entire, so near x_c the integrand is bounded by
|2z+n|·|E_n|·24e^{3π Im z} with no singular kernel, and the first polyline segment (start included) is covered by
the same (S2)-type bound h ≤ Re Ω − η as the rest of the far part.

## 2. Lemma 6 is formalised (2026-10-22, workstream W3) [Proved in Lean, given (S0)–(S5) as `SaddleData`]

`ZetaIrr.Z7.Analytic.size_of_saddleData` (Lemma 6(i): log|L_n| ≤ −G log n! + n(Vcert + o(1))) and
`nonvan_of_saddleData` (Lemma 6(ii)) in `lean_zeta7/ZetaIrrational/Z7/Analytic/NonvanZ7.lean`, standard axioms only,
via the route of §1 above. No gap in PROOF_ZETA §6 was found. Remarks for the write-up:
* §10 item 1 (Stirling forms (6.4.2)) is moot: only the log Γ expansion is used, with the DLMF-type constant of
  lean_beta's `Stirling/` (generalised to Γ-shifts β ∈ [0, 2], since the ζ factor list has β = 0 for Γ(z) and
  Γ(z + δn)).
* §10 item 4 (near-real-axis piece) is covered exactly as in lean_beta: (S2) on the first segment (`S2_first`, start
  point moved by |e| ≤ δ₀ along ℝ) bounds h = Re Ψ + 3π Im x there, because the integrand R_n k⁗ = (2z+n) E_n T has
  no singular kernel.
* The size bound uses Stirling's upper bound log n! ≤ n log n − n + (log n)/2 + 1 (Mathlib's `stirlingSeq`
  monotonicity) and only Re Ω ≤ −10.1167; constants are explicit but crude.

## 3. The Lean proof is complete (2026-10-22, main session) [Proved in Lean]

`lean_zeta7`: `ZetaIrr.Z7.oneOfZeta7To21 : ∃ j ∈ {7, 9, …, 21}, Irrational (riemannZeta j).re`, standard axioms only,
no `sorry`, no `native_decide`. The A-certificate in Lean equals the exact fraction of `f4_final.log`; the Lean saddle
enclosure is Re Ω ∈ [−10.1167486, −10.1167485]. Small points for PROOF_ZETA:
* §9 "events 30,971" for Z7: the event list has 30,138 points (30,137 intervals); 30,971 apparently counts chunk
  endpoints twice (workstream W2). The value of A is unaffected.
* Lemma A(b′) is only needed in its integrality form (a_{i,k} ∈ ℤ_p when no pole of a block lies at distance ≡ 0 mod p),
  and holds without p² > 𝒩 (W1), as review A had observed.
* The pointwise bound F_n(p) ≤ e*(n/p) of §5.1 holds for every prime p ≤ n, without √𝒩 < p (W1, W2).
* With the integration-by-parts route of §1 above, §6.1–6.6 formalised with no gap (W3); the steepest-descent
  certificate (S0)–(S5) formalised as written (W4).
