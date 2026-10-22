/-
# Z7 contour certificate: lower polyline (PROOF_ZETA §6.3, (S2), (S4), (S5))

Kernel checks (`decide +kernel`) on the segments of `dnStart, dnPts` (`PolyDataZ7.lean`), from
`x₀ - ρ d` down to the real point `x_c`:
* `chk_dn`: `Re f ≤ T0` on every segment (`polyChk`);
* `chk_sec_dn`: `|α_i| ≥ 1/100`, `|arg α_i| ≤ 2.76` for every factor and `Re z > -1/2`
  (`polySectorQ`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Interval.PolyDataZ7

namespace ZetaIrr.Z7.Interval

open ZetaIrr.Interval ZetaIrr.Fam.Interval

lemma chk_dn : polyChk 3 40 16 facZ7 T0 dnStart dnPts = true := by decide +kernel

lemma chk_sec_dn : polySectorQ 40 16 amin Amax facZ7 dnStart dnPts = true := by decide +kernel

end ZetaIrr.Z7.Interval
