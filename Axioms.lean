import ZetaIrrational

/-! # Axiom audit

Run with `lake env lean Axioms.lean` (after `lake build`). Every line should print only Lean's three
standard axioms `[propext, Classical.choice, Quot.sound]`. A `sorryAx` would indicate a gap, and a
`Lean.ofReduceBool` / `*.native_decide.ax_*` entry would indicate trust in the compiler.

-/

-- The main theorem
#print axioms ZetaIrr.Z7.oneOfZeta7To21

-- The statement and the conditional main theorem
#print axioms ZetaIrr.riemannZeta_re_eq_zetaR      -- `(riemannZeta s).re = Σ 1/(m+1)^s`
#print axioms ZetaIrr.oneOfZeta7To21_of_forms      -- small forms ⇒ the statement
#print axioms ZetaIrr.Z7.oneOfZeta7To21_of_hyp     -- Hyp ⇒ the statement

-- Lemmas 1–3 for partial-fraction data
#print axioms ZetaIrr.PFData.tsum_R4_odd

-- Lemma 6: size and nonvanishing from the kernel-checked saddle certificate
#print axioms ZetaIrr.Z7.Interval.Z7_saddleData       -- (S0)–(S5), (H4), Re Ω ≤ −10.1167
#print axioms ZetaIrr.Z7.Analytic.size_of_saddleData  -- Lemma 6(i) from SaddleData
#print axioms ZetaIrr.Z7.Analytic.nonvan_of_saddleData -- Lemma 6(ii) from SaddleData
#print axioms ZetaIrr.Z7.size_Z7
#print axioms ZetaIrr.Z7.nonvan_Z7

-- Lemmas 3–5 and the conditional assembly
#print axioms ZetaIrr.Z7.expansion_Z7                -- Lemma 3: L_n ∈ ℚ + ℚζ(7) + … + ℚζ(21)
#print axioms ZetaIrr.Z7.oneOfZeta7To21_of_parts     -- Lemmas 4–5 + assembly, given (H2)
#print axioms ZetaIrr.Z7.CertA.certFact_of_units     -- (H2) from the unit count
#print axioms ZetaIrr.Z7.oneOfZeta7To21_of_certUnits -- main theorem given the unit count
#print axioms ZetaIrr.Z7.CertA.bodyUnits_400         -- (H2) the kernel-checked A-certificate sum
