/-
# Z7 contour certificate: upper polyline, chunk 1 ((S2), (S4))

Kernel checks (`decide +kernel`) on the segments of `upStart, upC1` (`PolyDataZ7.lean`):
* `chk_up1`: `Re f ≤ T0` on every segment (`polyChk`, second-order Taylor bound per segment);
* `chk_sec_up1`: `|α_i| ≥ 1/100`, `|arg α_i| ≤ 2.76` for every factor and `Re z > -1/2`
  (`polySectorQ`).

Combined with the other chunks in `ContourZ7.lean`.
-/
import ZetaIrrational.Z7.Interval.PolyDataZ7

namespace ZetaIrr.Z7.Interval

open ZetaIrr.Interval ZetaIrr.Fam.Interval

lemma chk_up1 : polyChk 3 40 16 facZ7 T0 upStart upC1 = true := by decide +kernel

lemma chk_sec_up1 : polySectorQ 40 16 amin Amax facZ7 upStart upC1 = true := by decide +kernel

end ZetaIrr.Z7.Interval
