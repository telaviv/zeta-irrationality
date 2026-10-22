/-
# Instance Z7: one of ζ(7), ζ(9), …, ζ(21) is irrational, given the A-certificate sum

All inputs of `oneOfZeta7To21_of_parts` (`Z7/Glue/Main.lean`) are discharged except the single
computational fact `CertA.UnitsFact`: the rounded body sum `bodyUnits 400` of the A-certificate
(Lemma 5) has the stated value (with the tail, exactly `Acert`).
* Lemma 6(i), 6(ii): `size_Z7`, `nonvan_Z7` (`Z7/Lemma6.lean`).
-/
import ZetaIrrational.Z7.Glue.Main
import ZetaIrrational.Z7.Lemma6

namespace ZetaIrr.Z7

/-- **Main theorem for Z7, conditional on the A-certificate computation.** -/
theorem oneOfZeta7To21_of_certUnits (h : CertA.UnitsFact) : OneOfZeta7To21 := by
  obtain ⟨εL, hεL, hsize⟩ := size_Z7
  exact oneOfZeta7To21_of_parts (CertA.certFact_of_units h) εL hεL hsize nonvan_Z7

end ZetaIrr.Z7
