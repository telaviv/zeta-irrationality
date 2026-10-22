import ZetaIrrational

/-! # Axiom audit

Run with `lake env lean Axioms.lean` (after `lake build`). Every line should print only Lean's three
standard axioms `[propext, Classical.choice, Quot.sound]`. A `sorryAx` would indicate a gap, and a
`Lean.ofReduceBool` / `*.native_decide.ax_*` entry would indicate trust in the compiler.

The main theorem `ZetaIrr.Z7.oneOfZeta7To21` is not assembled yet; see PLAN.md. -/

-- The statement and the conditional main theorem
#print axioms ZetaIrr.riemannZeta_re_eq_zetaR      -- `(riemannZeta s).re = Σ 1/(m+1)^s`
#print axioms ZetaIrr.oneOfZeta7To21_of_forms      -- small forms ⇒ the statement
#print axioms ZetaIrr.Z7.oneOfZeta7To21_of_hyp     -- Hyp ⇒ the statement

-- Lemmas 1–3 for partial-fraction data
#print axioms ZetaIrr.PFData.tsum_R4_odd
