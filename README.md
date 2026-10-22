# lean_zeta7 — Lean 4 + Mathlib formalisation of "one of ζ(7), ζ(9), …, ζ(21) is irrational"

Target theorem (standard axioms only, no sorry, no native_decide):

    theorem oneOfZeta7To21 : ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), Irrational (riemannZeta j).re

Source mathematics: `../handoff/zeta7/PROOF_ZETA.md` (instance Z7: r = 11/12, 18 pole blocks at δ = k/80, q = 240,
certified Q ≤ −0.1981). Template: `../lean_beta/` (the β(4..36) formalisation, same toolchain, Lean/Mathlib v4.35.0).
Working notes: `../handoff/zeta7/ZETA7.md`.

Status: created 2026-10-21; nothing formalised yet.
