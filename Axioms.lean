import ZetaIrrational

/-! # Axiom audit

Run with `lake env lean Axioms.lean` (after `lake build`). Every line should print only Lean's three
standard axioms `[propext, Classical.choice, Quot.sound]`. A `sorryAx` would indicate a gap, and a
`Lean.ofReduceBool` / `*.native_decide.ax_*` entry would indicate trust in the compiler. -/

-- The main theorem
#print axioms ZetaIrr.Z7.oneOfZeta7To21

-- The statement and the irrationality criterion
#print axioms ZetaIrr.riemannZeta_re_eq_zetaR          -- `(riemannZeta s).re = Σ 1/(m+1)^s`
#print axioms ZetaIrr.oneOfZeta7To21_of_forms          -- small integer forms ⇒ the statement
#print axioms ZetaIrr.Z7.oneOfZeta7To21_of_hyp         -- Lemmas 3–6 ⇒ the statement

-- Lemmas 1–3
#print axioms ZetaIrr.PFData.tsum_R4_odd               -- for partial-fraction data
#print axioms ZetaIrr.Z7.expansion_Z7                  -- L_n ∈ ℚ + ℚζ(7) + … + ℚζ(21)

-- Lemmas 4–5
#print axioms ZetaIrr.Z7.oneOfZeta7To21_of_parts       -- denominators, prime sums, assembly
#print axioms ZetaIrr.Z7.CertA.certFact_of_units       -- the A bound from the unit count
#print axioms ZetaIrr.Z7.CertA.bodyUnits_400           -- the kernel-checked A-certificate sum

-- Lemma 6
#print axioms ZetaIrr.Z7.Interval.Z7_saddleData        -- the kernel-checked saddle data (S0)–(S5)
#print axioms ZetaIrr.Z7.Analytic.size_of_saddleData   -- Lemma 6(i) from saddle data
#print axioms ZetaIrr.Z7.Analytic.nonvan_of_saddleData -- Lemma 6(ii) from saddle data
#print axioms ZetaIrr.Z7.size_Z7
#print axioms ZetaIrr.Z7.nonvan_Z7
