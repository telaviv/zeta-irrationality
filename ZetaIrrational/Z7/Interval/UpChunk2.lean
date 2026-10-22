/-
# Z7 contour certificate: upper polyline, chunk 2 (PROOF_ZETA §6.3, (S2), (S4))

Kernel checks (`decide +kernel`) on the segments of `upA2, upC2` (`PolyDataZ7.lean`):
* `chk_up2`: `Re f ≤ T0` on every segment (`polyChk`, second-order Taylor bound per segment);
* `chk_sec_up2`: `|α_i| ≥ 1/100`, `|arg α_i| ≤ 2.76` for every factor and `Re z > -1/2`
  (`polySectorQ`).

Combined with the other chunks in `ContourZ7.lean`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Interval.PolyDataZ7

namespace ZetaIrr.Z7.Interval

open ZetaIrr.Interval ZetaIrr.Fam.Interval

lemma chk_up2 : polyChk 3 40 16 facZ7 T0 upA2 upC2 = true := by decide +kernel

lemma chk_sec_up2 : polySectorQ 40 16 amin Amax facZ7 upA2 upC2 = true := by decide +kernel

end ZetaIrr.Z7.Interval
